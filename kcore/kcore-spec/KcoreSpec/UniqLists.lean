/-
  KCore, checked layer: more clauses whose match fixes their variables (`clauseFixedL`), hence match
  independent (`clauseFixedL_sound`), than `clauseFixed` confirms.

  `uniq` (Uniq.lean) fixes the variables of constructor patterns, injections, aliases and map
  patterns `K |-> V M` whose key is fixed by the arguments before it. `uniqL` adds:
  - list patterns: `.List` binds nothing; `ListItem(P)` denotes the one-element list of P's value;
    `ListItem(P) L` denotes a list whose first element is P's value and whose rest is L's, so two
    matches at one list agree on P's value and on L's (whose sort, List, fixes the value's tag);
  - a lone map element `K |-> V`, which denotes the one-entry map: two matches agree on K's and V's
    values;
  - an overloading symbol `f(P̄)`, which denotes the normal form of its arguments' values: two
    matches agree on them (`norm_inj_ovlF`, at arguments of f's sorts);
  and `uniqArgs` reads the arguments in passes, each pass taking those whose map keys are fixed by
  the arguments taken before, so `lookup(K |-> V M, K)` is fixed (its key bound by the second
  argument). Reading the arguments in another order is sound because each argument's denotation is
  the same list element under both matches: the arguments' agreements compose in any order.

  `matchObligationsL` names the clauses `clauseFixedL` does not confirm; `matchIndependentAll_of_L`
  gives every clause's match independence from them.
-/
import KcoreSpec.MatchIndependent
import KcoreSpec.HypWf

set_option autoImplicit false

namespace KCore.Det

open KCore KCore.Exec GroundTerm

variable {c : Semantics}

mutual
  /-- `some D'`: two well-sorted σ, σ' under which p denotes one value, and that agree on D, agree
  on D' (`uniqL_sound`). -/
  def uniqL (c : Semantics) (D : List Nat) : Term → Option (List Nat)
    | .var i => some (i :: D)
    | .dv _ _ => some D
    | .inj _ _ p => uniqL c D p
    | .as p i => (uniqL c D p).map (i :: ·)
    | .app f ps =>
      if (lookupSig c.ctorSigs f).isSome then uniqLList c D ps
      else if f == listUnit then (if ps.isEmpty then some D else none)
      else if f == listElem then uniqLElem c D ps
      else if f == listConcat then uniqLCat c D ps
      else if f == mapElem then uniqLList c D ps
      else if (c.lookupOvl f).isSome && c.isOvl f then uniqLList c D ps
      else uniq c D (.app f ps)
    termination_by structural p => p
  def uniqLList (c : Semantics) (D : List Nat) : List Term → Option (List Nat)
    | [] => some D
    | p :: ps => (uniqL c D p).bind fun D' => uniqLList c D' ps
    termination_by structural ps => ps
  /-- `ListItem(P)`. -/
  def uniqLElem (c : Semantics) (D : List Nat) : List Term → Option (List Nat)
    | [p] => uniqL c D p
    | _ => none
    termination_by structural ps => ps
  /-- `ListItem(P) L`. -/
  def uniqLCat (c : Semantics) (D : List Nat) : List Term → Option (List Nat)
    | [.app e [p], rest] =>
      if e == listElem && !(lookupSig c.ctorSigs e).isSome then
        (uniqL c D p).bind fun D' => uniqL c D' rest
      else none
    | _ => none
    termination_by structural ps => ps
end

/-- One pass over the arguments: those `uniqL` accepts given the variables fixed so far, in order;
the others are returned for the next pass. -/
def uniqPass (c : Semantics) (D : List Nat) : List Term → List Nat × List Term
  | [] => (D, [])
  | p :: ps => match uniqL c D p with
    | some D' => uniqPass c D' ps
    | none => ((uniqPass c D ps).1, p :: (uniqPass c D ps).2)

/-- Passes over the arguments until none is left (`some D`), or the fuel runs out (`none`). -/
def uniqArgs (c : Semantics) : Nat → List Nat → List Term → Option (List Nat)
  | _, D, [] => some D
  | 0, _, _ :: _ => none
  | n + 1, D, p :: ps => uniqArgs c n (uniqPass c D (p :: ps)).1 (uniqPass c D (p :: ps)).2

/-- The clause's match fixes every variable: `clauseFixed` with list patterns, lone map elements
and the arguments read in passes (`uniqArgs`). -/
def _root_.KCore.Semantics.clauseFixedL (c : Semantics) (cl : Clause) : Bool :=
  match uniqArgs c (cl.pats.length + 1) [] cl.pats with
  | some D => (List.range cl.vars.length).all D.contains
  | none => false

/-- The clauses `clauseFixedL` does not confirm, as functions and indices (`matchObligations`'s
form): that each is match independent is a named obligation. -/
def _root_.KCore.Semantics.matchObligationsL (c : Semantics) : List (Sym × Nat) :=
  c.fns.flatMap fun f =>
    ((List.range f.clauses.length).filter fun i => !(f.clauses[i]?.all c.clauseFixedL)).map
      (f.label, ·)

/-! ## Soundness -/

theorem isCtor_of_lookup {f : Sym} (h : (lookupSig c.ctorSigs f).isSome = false) : c.isCtor f = false := by
  simpa [Semantics.isCtor] using h

theorem isCollPat_list {f : Sym} (hf : f ∈ listPatternHooks) : c.isCollPat f = true := by
  simp only [listPatternHooks, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl <;> rfl

theorem hook_listElem_eq (vs : List GroundTerm) :
    hook listElem vs = some (match vs with | [k] => some (.list Srt.list [k]) | _ => none) := rfl
theorem hook_listUnit_eq (vs : List GroundTerm) :
    hook listUnit vs = some (match vs with | [] => some (.list Srt.list []) | _ => none) := rfl
theorem hook_listConcat_eq (vs : List GroundTerm) :
    hook listConcat vs = some (match vs with
      | [.list _ a, .list _ b] => some (.list Srt.list (a ++ b)) | _ => none) := rfl

theorem collVal_listElem {vs : List GroundTerm} {v : GroundTerm} (h : c.collVal listElem vs = some v) :
    ∃ w, vs = [w] ∧ v = .list Srt.list [w] := by
  unfold Semantics.collVal at h
  rw [if_pos (by decide), hook_listElem_eq] at h
  match vs, h with
  | [w], h => exact ⟨w, rfl, by simpa using h.symm⟩
  | [], h => simp at h
  | _ :: _ :: _, h => simp at h

theorem collVal_listConcat {vs : List GroundTerm} {v : GroundTerm} (h : c.collVal listConcat vs = some v) :
    ∃ s a t b, vs = [.list s a, .list t b] ∧ v = .list Srt.list (a ++ b) := by
  unfold Semantics.collVal at h
  rw [if_pos (by decide), hook_listConcat_eq] at h
  match vs, h with
  | [.list s a, .list t b], h => exact ⟨s, a, t, b, rfl, by simpa using h.symm⟩
  | [], h => simp at h
  | [_], h => simp at h
  | _ :: _ :: _ :: _, h => simp at h
  | [.ctor _ _, _], h => simp at h
  | [.inj _ _ _, _], h => simp at h
  | [.dv _ _, _], h => simp at h
  | [.map _ _, _], h => simp at h
  | [.set _ _, _], h => simp at h
  | [.list _ _, .ctor _ _], h => simp at h
  | [.list _ _, .inj _ _ _], h => simp at h
  | [.list _ _, .dv _ _], h => simp at h
  | [.list _ _, .map _ _], h => simp at h
  | [.list _ _, .set _ _], h => simp at h

theorem sortOf_list_tag {s t : Srt} {es : List GroundTerm} (h : c.sortOf (.list s es) = some t) : s = t := by
  rw [Semantics.sortOf] at h
  split at h
  · split at h
    · exact Option.some.inj h
    · cases h
  · cases h

theorem sig_listConcat : lookupSig hookSigs listConcat = some ⟨listConcat, [Srt.list, Srt.list], Srt.list⟩ := by decide

/-- The signature of `_List_` in a left-hand side's context, where no constructor bears its number:
two lists, a list. -/
theorem patCtxNF_listConcat {vars : List Srt} {ps : List Term} {s : Srt}
    (hct : c.isCtor listConcat = false) (ht : sortOfTerm c.patCtxNF vars (.app listConcat ps) = some s) :
    sortsOfTerms c.patCtxNF vars ps = some [Srt.list, Srt.list] := by
  obtain ⟨k, hk', hargs, rfl⟩ := sortOfTerm_app.mp ht
  rcases patCtxNF_collPat_lookup hct (isCollPat_list (by decide)) hk' with ⟨-, hk⟩ | ⟨hh, -⟩
  · rw [sig_listConcat] at hk
    cases hk
    exact hargs
  · cases hh

theorem uniqLCat_inv {D D' : List Nat} {ps : List Term} (h : uniqLCat c D ps = some D') :
    ∃ e p rest, ps = [.app e [p], rest] := by
  unfold uniqLCat at h
  split at h
  · exact ⟨_, _, _, rfl⟩
  · cases h

mutual
  theorem uniqL_sound (hmc : MatchCtxO c) {σ σ' : Subst} {vars : List Srt}
      (hσ : c.WellSorted vars σ) (hσ' : c.WellSorted vars σ') :
      ∀ (p : Term) {D D' : List Nat} {v : GroundTerm} {s : Srt}, uniqL c D p = some D' →
        PatVal c σ p v → PatVal c σ' p v → sortOfTerm c.patCtxNF vars p = some s →
        (∀ i ∈ D, σ.lookup i = σ'.lookup i) → ∀ i ∈ D', σ.lookup i = σ'.lookup i
    | .var j, D, D', v, s, hu, h, h', _, hD => by
      simp only [uniqL, Option.some.injEq] at hu
      subst hu
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · rw [PatVal.var_inv h, PatVal.var_inv h']
      · exact hD i hi
    | .dv _ _, D, D', v, s, hu, _, _, _, hD => by
      simp only [uniqL, Option.some.injEq] at hu
      subst hu; exact hD
    | .inj a b p, D, D', v, s, hu, h, h', hs, hD => by
      simp only [uniqL] at hu
      obtain ⟨w, hw, rfl⟩ := PatVal.inj_inv h
      obtain ⟨w', hw', he⟩ := PatVal.inj_inv h'
      obtain ⟨-, hps, -⟩ := sortOfTerm_inj.mp hs
      have := injNormal_inj hmc (patVal_sortedAll hmc hσ hw hps) (patVal_sortedAll hmc hσ' hw' hps) he
      subst this
      exact uniqL_sound hmc hσ hσ' p hu hw hw' hps hD
    | .as p j, D, D', v, s, hu, h, h', hs, hD => by
      simp only [uniqL, Option.map_eq_some_iff] at hu
      obtain ⟨D'', hu, rfl⟩ := hu
      obtain ⟨hp, hj⟩ := PatVal.as_inv h
      obtain ⟨hp', hj'⟩ := PatVal.as_inv h'
      have ih := uniqL_sound hmc hσ hσ' p hu hp hp' (sortOfTerm_as hs).2 hD
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · rw [hj, hj']
      · exact ih i hi
    | .app f ps, D, D', v, s, hu, h, h', hs, hD => by
      simp only [uniqL] at hu
      split at hu
      · rename_i hf
        obtain ⟨vs, rfl, hvs⟩ := PatVal.ctor_shape hmc hf h
        obtain ⟨vs', he, hvs'⟩ := PatVal.ctor_shape hmc hf h'
        cases he
        obtain ⟨k, -, hk, -⟩ := sortOfTerm_app.mp hs
        exact uniqLList_sound hmc hσ hσ' ps hu hvs hvs' hk hD
      rename_i hnc
      have hct : c.isCtor f = false := isCtor_of_lookup (by simpa using hnc)
      split at hu
      · -- `.List`
        rename_i hfu
        have hfu := beq_iff_eq.mp hfu
        subst hfu
        split at hu
        · simp only [Option.some.injEq] at hu; subst hu; exact hD
        · cases hu
      split at hu
      · -- `ListItem(P)`
        rename_i hfe
        have hfe := beq_iff_eq.mp hfe
        subst hfe
        obtain ⟨vs, hvs, hv⟩ := PatVal.coll_inv hct (isCollPat_list (by decide)) h
        obtain ⟨vs', hvs', hv'⟩ := PatVal.coll_inv hct (isCollPat_list (by decide)) h'
        obtain ⟨w, rfl, rfl⟩ := collVal_listElem hv
        obtain ⟨w', rfl, he⟩ := collVal_listElem hv'
        simp only [GroundTerm.list.injEq, List.cons.injEq, and_true, true_and] at he
        subst he
        obtain ⟨k, -, hk, -⟩ := sortOfTerm_app.mp hs
        exact uniqLElem_sound hmc hσ hσ' ps hu hvs hvs' hk hD
      split at hu
      · -- `ListItem(P) L`
        rename_i hfc
        have hfc := beq_iff_eq.mp hfc
        subst hfc
        exact uniqLCat_sound hmc hσ hσ' ps hct hu h h' hs hD
      split at hu
      · -- `K |-> V`
        rename_i hfm
        have hfm := beq_iff_eq.mp hfm
        subst hfm
        obtain ⟨vs, hvs, hv⟩ := PatVal.hook_inv hct (by decide) h
        obtain ⟨vs', hvs', hv'⟩ := PatVal.hook_inv hct (by decide) h'
        obtain ⟨k, w, rfl, rfl⟩ := hook_elem_inv hv
        obtain ⟨k', w', rfl, he⟩ := hook_elem_inv hv'
        simp only [GroundTerm.map.injEq, List.cons.injEq, Prod.mk.injEq, and_true, true_and] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨kk, -, hk, -⟩ := sortOfTerm_app.mp hs
        exact uniqLList_sound hmc hσ hσ' ps hu hvs hvs' hk hD
      split at hu
      · -- an overloading symbol: the normal form determines its arguments' values (`norm_inj_ovlF`)
        rename_i hfo
        simp only [Bool.and_eq_true] at hfo
        obtain ⟨vs, hvs, hv⟩ := PatVal.ovl_inv hfo.2 h
        obtain ⟨vs', hvs', hv'⟩ := PatVal.ovl_inv hfo.2 h'
        obtain ⟨k, hk', hargs, -⟩ := sortOfTerm_app.mp hs
        obtain ⟨o, hlo, rfl⟩ := patCtxNF_ovl_lookup hfo.2 hk'
        have he := OvlLaws.norm_inj_ovlF hmc.ovlHyp hmc.ovlHyp.fnFacts hlo (patVals_sortedAllO hmc hσ hvs hargs)
          (patVals_sortedAllO hmc hσ' hvs' hargs) (OvlLaws.fnCover_none_of_not_fnOvl (patCtxNF_lookup.mp hk').2 _)
          (OvlLaws.fnCover_none_of_not_fnOvl (patCtxNF_lookup.mp hk').2 _) (hv.trans hv'.symm)
        subst he
        exact uniqLList_sound hmc hσ hσ' ps hu hvs hvs' hargs hD
      · exact uniq_sound hmc hσ hσ' (.app f ps) hu h h' hs hD
  theorem uniqLList_sound (hmc : MatchCtxO c) {σ σ' : Subst} {vars : List Srt}
      (hσ : c.WellSorted vars σ) (hσ' : c.WellSorted vars σ') :
      ∀ (ps : List Term) {D D' : List Nat} {vs : List GroundTerm} {ss : List Srt},
        uniqLList c D ps = some D' → PatVals c σ ps vs → PatVals c σ' ps vs →
        sortsOfTerms c.patCtxNF vars ps = some ss →
        (∀ i ∈ D, σ.lookup i = σ'.lookup i) → ∀ i ∈ D', σ.lookup i = σ'.lookup i
    | [], D, D', vs, ss, hu, _, _, _, hD => by
      simp only [uniqLList, Option.some.injEq] at hu
      subst hu; exact hD
    | p :: ps, D, D', vs, ss, hu, h, h', hs, hD => by
      simp only [uniqLList, Option.bind_eq_some_iff] at hu
      obtain ⟨D'', hu₁, hu₂⟩ := hu
      obtain ⟨v, vs₁, rfl, h1, h2⟩ := PatVals.cons_inv' h
      obtain ⟨v', vs₁', he, h1', h2'⟩ := PatVals.cons_inv' h'
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨s₁, ss₁, hs₁, hs₂, -⟩ := sortsOfTerms_cons.mp hs
      exact uniqLList_sound hmc hσ hσ' ps hu₂ h2 h2' hs₂ (uniqL_sound hmc hσ hσ' p hu₁ h1 h1' hs₁ hD)
  theorem uniqLElem_sound (hmc : MatchCtxO c) {σ σ' : Subst} {vars : List Srt}
      (hσ : c.WellSorted vars σ) (hσ' : c.WellSorted vars σ') :
      ∀ (ps : List Term) {D D' : List Nat} {vs : List GroundTerm} {ss : List Srt},
        uniqLElem c D ps = some D' → PatVals c σ ps vs → PatVals c σ' ps vs →
        sortsOfTerms c.patCtxNF vars ps = some ss →
        (∀ i ∈ D, σ.lookup i = σ'.lookup i) → ∀ i ∈ D', σ.lookup i = σ'.lookup i
    | [p], D, D', vs, ss, hu, h, h', hs, hD => by
      simp only [uniqLElem] at hu
      obtain ⟨v, _, rfl, h1, -⟩ := PatVals.cons_inv' h
      obtain ⟨v', _, he, h1', -⟩ := PatVals.cons_inv' h'
      simp only [List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he
      obtain ⟨s₁, _, hs₁, -, -⟩ := sortsOfTerms_cons.mp hs
      exact uniqL_sound hmc hσ hσ' p hu h1 h1' hs₁ hD
    | [], _, _, _, _, hu, _, _, _, _ => by simp [uniqLElem] at hu
    | _ :: _ :: _, _, _, _, _, hu, _, _, _, _ => by simp [uniqLElem] at hu
  theorem uniqLCat_sound (hmc : MatchCtxO c) {σ σ' : Subst} {vars : List Srt}
      (hσ : c.WellSorted vars σ) (hσ' : c.WellSorted vars σ') :
      ∀ (ps : List Term) {D D' : List Nat} {v : GroundTerm} {s : Srt}, c.isCtor listConcat = false →
        uniqLCat c D ps = some D' →
        PatVal c σ (.app listConcat ps) v → PatVal c σ' (.app listConcat ps) v →
        sortOfTerm c.patCtxNF vars (.app listConcat ps) = some s →
        (∀ i ∈ D, σ.lookup i = σ'.lookup i) → ∀ i ∈ D', σ.lookup i = σ'.lookup i
    | [.app e [p], rest], D, D', v, s, hct, hu, h, h', hs, hD => by
      simp only [uniqLCat] at hu
      split at hu
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
        obtain ⟨rfl, hne⟩ := hc
        have hcte : c.isCtor listElem = false := isCtor_of_lookup hne
        simp only [Option.bind_eq_some_iff] at hu
        obtain ⟨D'', hu₁, hu₂⟩ := hu
        obtain ⟨vs, hvs, hv⟩ := PatVal.coll_inv hct (isCollPat_list (by decide)) h
        obtain ⟨vs', hvs', hv'⟩ := PatVal.coll_inv hct (isCollPat_list (by decide)) h'
        obtain ⟨s₁, a, t, b, rfl, rfl⟩ := collVal_listConcat hv
        obtain ⟨s₁', a', t', b', rfl, he⟩ := collVal_listConcat hv'
        obtain ⟨_, _, he1, hE, hRa⟩ := PatVals.cons_inv' hvs
        obtain ⟨_, _, he2, hR, -⟩ := PatVals.cons_inv' hRa
        cases he1; cases he2
        obtain ⟨_, _, he3, hE', hRc⟩ := PatVals.cons_inv' hvs'
        obtain ⟨_, _, he4, hR', -⟩ := PatVals.cons_inv' hRc
        cases he3; cases he4
        obtain ⟨ws, hws, hw⟩ := PatVal.coll_inv hcte (isCollPat_list (by decide)) hE
        obtain ⟨ws', hws', hw'⟩ := PatVal.coll_inv hcte (isCollPat_list (by decide)) hE'
        obtain ⟨w, rfl, hw⟩ := collVal_listElem hw
        obtain ⟨w', rfl, hw'⟩ := collVal_listElem hw'
        cases hw; cases hw'
        simp only [GroundTerm.list.injEq, List.cons_append, List.nil_append, List.cons.injEq] at he
        obtain ⟨-, rfl, rfl⟩ := he
        obtain ⟨hsE, hsR⟩ := sortsOfTerms_two (patCtxNF_listConcat hct hs)
        have ht := sortOf_list_tag (patVal_sortedAll hmc hσ hR hsR)
        have ht' := sortOf_list_tag (patVal_sortedAll hmc hσ' hR' hsR)
        subst ht ht'
        obtain ⟨_, _, he5, hP, -⟩ := PatVals.cons_inv' hws
        obtain ⟨_, _, he6, hP', -⟩ := PatVals.cons_inv' hws'
        cases he5; cases he6
        obtain ⟨ke, -, hargsE, -⟩ := sortOfTerm_app.mp hsE
        obtain ⟨sp, _, hsP, -, -⟩ := sortsOfTerms_cons.mp hargsE
        exact uniqL_sound hmc hσ hσ' rest hu₂ hR hR' hsR (uniqL_sound hmc hσ hσ' p hu₁ hP hP' hsP hD)
      · cases hu
    | [], _, _, _, _, _, hu, _, _, _, _ | [_], _, _, _, _, _, hu, _, _, _, _
    | _ :: _ :: _ :: _, _, _, _, _, _, hu, _, _, _, _
    | [.var _, _], _, _, _, _, _, hu, _, _, _, _ | [.dv _ _, _], _, _, _, _, _, hu, _, _, _, _
    | [.inj _ _ _, _], _, _, _, _, _, hu, _, _, _, _ | [.as _ _, _], _, _, _, _, _, hu, _, _, _, _
    | [.app _ [], _], _, _, _, _, _, hu, _, _, _, _
    | [.app _ (_ :: _ :: _), _], _, _, _, _, _, hu, _, _, _, _ => by
      obtain ⟨_, _, _, he⟩ := uniqLCat_inv hu
      simp at he
end

/-- Each argument of a list, with its value under both matches. -/
theorem patVals_pairs {σ σ' : Subst} : ∀ {ps : List Term} {vs : List GroundTerm},
    PatVals c σ ps vs → PatVals c σ' ps vs → ∀ p ∈ ps, ∃ v, PatVal c σ p v ∧ PatVal c σ' p v
  | [], _, _, _, _, h => nomatch h
  | q :: qs, _, h, h', p, hp => by
    obtain ⟨v, vs, rfl, h1, h2⟩ := PatVals.cons_inv' h
    obtain ⟨v', vs', he, h1', h2'⟩ := PatVals.cons_inv' h'
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨v, h1, h1'⟩
    · exact patVals_pairs h2 h2' p hp

theorem sortsOfTerms_each {x : TermCtx} {vars : List Srt} : ∀ {ps : List Term} {ss : List Srt},
    sortsOfTerms x vars ps = some ss → ∀ p ∈ ps, ∃ s, sortOfTerm x vars p = some s
  | [], _, _, _, h => nomatch h
  | q :: qs, _, hs, p, hp => by
    obtain ⟨s, ss, h1, h2, -⟩ := sortsOfTerms_cons.mp hs
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨s, h1⟩
    · exact sortsOfTerms_each h2 p hp

/-- What a pass over arguments, each denoting one value under both matches, fixes; the arguments it
returns are among those it was given. -/
theorem uniqPass_sound (hmc : MatchCtxO c) {σ σ' : Subst} {vars : List Srt}
    (hσ : c.WellSorted vars σ) (hσ' : c.WellSorted vars σ') :
    ∀ (ps : List Term) {D : List Nat},
      (∀ p ∈ ps, (∃ v, PatVal c σ p v ∧ PatVal c σ' p v) ∧ ∃ s, sortOfTerm c.patCtxNF vars p = some s) →
      (∀ i ∈ D, σ.lookup i = σ'.lookup i) →
      (∀ i ∈ (uniqPass c D ps).1, σ.lookup i = σ'.lookup i) ∧ (∀ p ∈ (uniqPass c D ps).2, p ∈ ps)
  | [], D, _, hD => by simpa [uniqPass] using hD
  | p :: ps, D, hps, hD => by
    have hrest : ∀ q ∈ ps, (∃ v, PatVal c σ q v ∧ PatVal c σ' q v) ∧
        ∃ s, sortOfTerm c.patCtxNF vars q = some s := fun q hq => hps q (List.mem_cons_of_mem _ hq)
    unfold uniqPass
    split
    · rename_i D' hu
      obtain ⟨⟨v, h, h'⟩, s, hs⟩ := hps p (List.mem_cons_self ..)
      obtain ⟨h1, h2⟩ := uniqPass_sound hmc hσ hσ' ps hrest (uniqL_sound hmc hσ hσ' p hu h h' hs hD)
      exact ⟨h1, fun q hq => List.mem_cons_of_mem _ (h2 q hq)⟩
    · obtain ⟨h1, h2⟩ := uniqPass_sound hmc hσ hσ' ps hrest hD
      refine ⟨h1, fun q hq => ?_⟩
      rcases List.mem_cons.mp hq with rfl | hq
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (h2 q hq)

theorem uniqArgs_sound (hmc : MatchCtxO c) {σ σ' : Subst} {vars : List Srt}
    (hσ : c.WellSorted vars σ) (hσ' : c.WellSorted vars σ') :
    ∀ (n : Nat) (ps : List Term) {D D' : List Nat}, uniqArgs c n D ps = some D' →
      (∀ p ∈ ps, (∃ v, PatVal c σ p v ∧ PatVal c σ' p v) ∧ ∃ s, sortOfTerm c.patCtxNF vars p = some s) →
      (∀ i ∈ D, σ.lookup i = σ'.lookup i) → ∀ i ∈ D', σ.lookup i = σ'.lookup i
  | _, [], D, D', hu, _, hD => by
    unfold uniqArgs at hu
    · simp only [Option.some.injEq] at hu; subst hu; exact hD
  | 0, _ :: _, _, _, hu, _, _ => by simp [uniqArgs] at hu
  | n + 1, p :: ps, D, D', hu, hps, hD => by
    simp only [uniqArgs] at hu
    obtain ⟨h1, h2⟩ := uniqPass_sound hmc hσ hσ' (p :: ps) hps hD
    exact uniqArgs_sound hmc hσ hσ' n _ hu (fun q hq => hps q (h2 q hq)) h1

/-- **A clause without existential variables that `clauseFixedL` accepts is match independent**: its patterns, well sorted in a
left-hand side's context, fix all of its variables (`uniqArgs_sound`), and its right-hand side's
and its `ensures`' are among them. -/
theorem clauseFixedL_sound {cl : Clause} {ss : List Srt} {x : TermCtx} {s : Srt} (hmc : MatchCtxO c)
    (hpt : sortsOfTerms c.patCtxNF cl.vars cl.pats = some ss)
    (hrt : sortOfTerm x cl.vars cl.rhs = some s) (hens : reqOK x cl.vars cl.ens = true)
    (hfx : c.clauseFixedL cl = true) (hx : cl.exs = []) :
    MatchIndependent c cl := by
  refine ⟨?_, fun hne => absurd hx hne⟩
  intro vs σ σ' ⟨hσ, hm, _⟩ ⟨hσ', hm', _⟩ _ _ _ _ _
  unfold Semantics.clauseFixedL at hfx
  split at hfx
  · rename_i D hD
    simp only [List.all_eq_true, List.contains_iff_mem, List.mem_range] at hfx
    have hag : ∀ i, i < cl.vars.length → σ.lookup i = σ'.lookup i := fun i hi =>
      uniqArgs_sound hmc ((wellSortedAt_univ hx).mp hσ) ((wellSortedAt_univ hx).mp hσ') _ cl.pats hD
        (fun p hp => ⟨patVals_pairs hm hm' p hp, sortsOfTerms_each hpt p hp⟩) (fun _ h => by cases h) i (hfx i hi)
    refine .inl ⟨hx, hx, rfl, rfl, fun i hi => hag i (sortOfTerm_vars hrt i hi), fun t ht i hi => ?_⟩
    rw [ht] at hens
    exact hag i (sortOfTerm_vars (reqOK_some hens) i hi)
  · cases hfx

/-- Each clause `matchObligationsL` names is match independent: the obligation, in
`MatchObligations`'s form. -/
def MatchObligationsL (c : Semantics) : Prop :=
  ∀ p ∈ c.matchObligationsL, ∀ fn, c.lookupFn p.1 = some fn → ∀ cl, fn.clauses[p.2]? = some cl →
    MatchIndependent c cl

/-- **Every clause is match independent** in a core that `sortedOK` accepts, with the matcher's
facts `MatchCtxO` (overloading symbols admitted), given the obligations `matchObligationsL` names: a
clause `clauseFixedL` confirms by `clauseFixedL_sound`, the others by their obligation; the sort
predicates' clauses are fixed. -/
theorem matchIndependentAll_of_L (hok : c.sortedOK = true) (hmc : MatchCtxO c)
    (hob : MatchObligationsL c) : MatchIndependentAll c := by
  intro f fn hfn cl hcl
  obtain ⟨hmem, hlab⟩ := lookupFn_spec hfn
  obtain ⟨hpt, -, L, -, -, hrt, hens⟩ := Faithful.clause_ctxOccE hok hmem hcl
  have hens' : reqOK (c.rhsCtx L) cl.vars cl.ens = true := by
    cases he : cl.ens with
    | none => rfl
    | some t => simpa [reqOK, he] using hens t he
  rcases List.mem_append.mp hmem with hf | hp
  · cases hfx : c.clauseFixedL cl with
    | true => exact clauseFixedL_sound hmc (Semantics.pats_nf hmc.ovlHyp hmem hcl hpt) hrt hens' hfx (Semantics.sortedOK_plainCl hok fn hmem cl hcl).1
    | false =>
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcl
      refine hob (fn.label, i) ?_ fn (by rw [hlab]; exact hfn) _ (List.getElem?_eq_getElem hi)
      simp only [Semantics.matchObligationsL, List.mem_flatMap, List.mem_map, List.mem_filter,
        List.mem_range, Prod.mk.injEq]
      refine ⟨fn, hf, i, ⟨hi, ?_⟩, rfl, rfl⟩
      simp [List.getElem?_eq_getElem hi, hfx]
  · cases hfx : c.clauseFixed cl with
    | true => exact clauseFixed_sound hmc (Semantics.pats_nf hmc.ovlHyp hmem hcl hpt) hrt hens' hfx (Semantics.sortedOK_plainCl hok fn hmem cl hcl).1
    | false => exact absurd (sortPreds_fixed hp cl hcl) (by rw [hfx]; decide)

kernel_rfl Semantics.matchObligationsL_withHooks :
  ∀ (c : Semantics) (H : HookParams), (c.withHooks H).matchObligationsL = c.matchObligationsL

end KCore.Det
