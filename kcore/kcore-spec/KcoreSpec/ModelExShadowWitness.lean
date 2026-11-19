/-
  KCore. A semantics that meets every condition of `coreOK` but `clausesPlain`, and `FnHyp`, whose
  `Γ` has no model because an existential variable of a clause's right side is a variable of its
  left side: so `SoundC` fails of it (`not_sound`), and `clausesPlain` cannot be left out of
  `coreOK`.

  Its own sort `N` has the constants `a` and `b`, and its function `f : N → N` has two clauses of
  one priority:
  - `f(a #as X) => X`, with `X` listed among the existential variables of its right side;
  - `f(X) => X`.
  `Eval` reads the first as `f(a) = a`: the existential variables an instance varies are those the
  left side does not hold (`Clause.exsFree`), and the left side holds `X`. So the two clauses agree
  and `FnHyp` holds. The first clause's equation is `X0 ∈ (a ∧ X) → f(X0) = ∃X. X` (`clauseRhs`
  binds every existential variable on the right): `f(a)` holds every element of `N`, `b`'s among
  them; the second's makes `f(a)` the element of `a` alone. The elements of the distinct values
  `a` and `b` are distinct (`values_apart`), so no model meets both. clausesPlain's `clauseExOK`
  (an existential variable is in no pattern or condition of the left side) refuses exactly this;
  its other parts hold (`only_left`). The decidable facts are kernel decisions.
-/
import KcoreSpec.Sound
import KcoreSpec.CoreDecide
import KcoreSpec.ClauseExDen
import KcoreSpec.FaithfulNeg
import KcoreSpec.FaithfulStage4
import KcoreSpec.FaithfulStep
import KcoreSpec.ModelCons
import KcoreSpec.ModelFnsEx
import KcoreSpec.ModelUndefRhsWitness

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace ExShadowWitness

open ML Faithful
open Faithful.UndefRhsWitness (cellSorts cellSubsorts)

/-- The own sort `N`, after `KCell` and `KCellOpt`. -/
def N : Srt := nRegSorts + 2
/-- The constants `a`, `b : → N` and the function `f`, after the three sort predicates, `<k>` and
`noKCell`. -/
def aL : Sym := nRegSyms + 5
def bL : Sym := nRegSyms + 6
def F : Sym := nRegSyms + 7

/-- `f(a #as X) => X`, `X` an existential variable of the right side. -/
def clA : Clause := ⟨[N], [.as (.app aL []) 0], none, .var 0, none, 50, false, [0], .top, .top⟩
/-- `f(X) => X`. -/
def clB : Clause := ⟨[N], [.var 0], none, .var 0, none, 50, false, [], .top, .top⟩
def fF : Fn := ⟨F, [N], N, [clA, clB], false⟩

def cellCtorsN : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 3, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 4, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt", "N"]
    symNames := ["LblisKCell", "LblisKCellOpt", "LblisN", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lbla", "Lblb",
      "Lblf"]
    userSorts := cellSorts ++ [N]
    ctors := cellCtorsN ++ [⟨aL, [], N⟩, ⟨bL, [], N⟩]
    fns := [fF]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

instance : OvlOK c := .of_nil rfl (by decide +kernel)

theorem lookupF : c.lookupFn F = some fF := rfl
theorem mem_fns {fn : Fn} (h : fn ∈ c.fns) : fn = fF := List.mem_singleton.mp h
theorem cl_of {cl : Clause} (h : cl ∈ fF.clauses) : cl = clA ∨ cl = clB := by simpa [fF] using h

def va : GroundTerm := .ctor aL []
def vb : GroundTerm := .ctor bL []
theorem va_sort : c.sortOf va = some N := by decide +kernel
theorem vb_sort : c.sortOf vb = some N := by decide +kernel

/-! ## Evaluation -/

/-- The pattern `a` denotes `a` alone. -/
theorem patA_inv {σ : Subst} {v : GroundTerm} (h : PatVal c σ (.app aL []) v) : v = va := by
  cases h with
  | ctor _ hs => cases hs; rfl
  | hook hp _ _ => exact absurd hp (by decide +kernel)
  | coll hc _ _ _ => exact absurd hc (by decide +kernel)
  | ovl hc _ _ _ => exact absurd hc (by decide +kernel)

/-- A match of a clause of `f` gives `X` the one argument. -/
theorem match_X {cl : Clause} (hcl : cl = clA ∨ cl = clB) {σ : Subst} {vs : List GroundTerm}
    (h : PatVals c σ cl.pats vs) : ∃ v, vs = [v] ∧ σ.lookup 0 = some v := by
  rcases hcl with rfl | rfl
  · obtain ⟨v, vs', rfl, hv, hs⟩ := PatVals.cons_inv h
    rw [PatVals.nil_inv hs]
    exact ⟨v, rfl, (PatVal.as_inv hv).2⟩
  · obtain ⟨v, vs', rfl, hv, hs⟩ := PatVals.cons_inv h
    rw [PatVals.nil_inv hs]
    exact ⟨v, rfl, PatVal.var_inv hv⟩

/-- A match of the first clause gives `X` the value `a`. -/
theorem matchA {σ : Subst} {vs : List GroundTerm} (h : PatVals c σ clA.pats vs) : σ.lookup 0 = some va := by
  obtain ⟨v, vs', rfl, hv, -⟩ := PatVals.cons_inv h
  have h2 := PatVal.as_inv hv
  rw [h2.2, patA_inv h2.1]

theorem exsFree_A : clA.exsFree = [] := by decide

/-- A result of a clause of `f` under σ is `X`'s value. -/
theorem res_eq {cl : Clause} (hcl : cl = clA ∨ cl = clB) {σ : Subst} {v : GroundTerm} (hl : σ.lookup 0 = some v)
    {r : Option GroundTerm} (h : cl.Res c σ r) : r = some v := by
  rcases hcl with rfl | rfl
  · rcases h with ⟨hx, -⟩ | ⟨-, h⟩
    · exact absurd hx (by decide)
    · have hag0 : ∀ σ' : Subst, AgreeOff clA.exsFree σ σ' → σ'.lookup 0 = some v := fun σ' hag => by
        rw [hag 0 (by rw [exsFree_A]; exact List.not_mem_nil), hl]
      rcases h with ⟨σ', w, hag, -, ⟨hrhs, -, -⟩, -, rfl⟩ | ⟨rfl, ⟨σ', hag, hws⟩, hall⟩
      · rw [EvalTerm.var_inv hrhs, hag0 σ' hag]
      · cases hall σ' hag hws with
        | fails _ hf =>
          cases hf with
          | ens ht => cases ht
          | post hp => exact absurd (Holds.top_eq hp) (by decide)
          | rhs hr => exact absurd ((EvalTerm.var_inv hr).trans (hag0 σ' hag)) (by simp)
  · rcases h with ⟨-, ⟨-, -, hrhs⟩ | ⟨t, w, ht, -⟩⟩ | ⟨hx, -⟩
    · rw [EvalTerm.var_inv hrhs, hl]
    · cases ht
    · exact absurd rfl hx

/-- Any two clauses of `f` are coherent: both give the argument. -/
theorem coh {cl cl' : Clause} (hcl : cl = clA ∨ cl = clB) (hcl' : cl' = clA ∨ cl' = clB) : Coherent c cl cl' := by
  intro vs σ σ' ha ha' _ _ _ _ _
  obtain ⟨v, rfl, hl⟩ := match_X hcl ha.2.1
  obtain ⟨v', hv', hl'⟩ := match_X hcl' ha'.2.1
  simp only [List.cons.injEq, and_true] at hv'
  subst hv'
  exact .inr fun r r' h h' => (res_eq hcl hl h).trans (res_eq hcl' hl' h').symm

theorem sg_sorted {σ : Subst} {v : GroundTerm} (hl : σ.lookup 0 = some v) (hv : c.sortOf v = some N) :
    c.WellSorted [N] σ := by
  intro i s hs
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨v, hl, hv⟩
  | succ i => simp at hs

theorem var_eval {σ : Subst} {v : GroundTerm} (hl : σ.lookup 0 = some v) : EvalTerm c σ (.var 0) (some v) := by
  have h := EvalTerm.var (c := c) (σ := σ) (i := 0)
  rwa [hl] at h

/-- **`f(v)` is `v`**, by the second clause. -/
theorem eval_B {v : GroundTerm} (hv : c.sortOf v = some N) : Eval c F [v] (some v) :=
  .clause (fn := fF) (cl := clB) (σ := [(0, v)]) lookupF (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    (sg_sorted rfl hv) (.cons (.var rfl) .nil) (fun _ ht => nomatch ht) .top
    (fun cl' hcl' _ hlt => by rcases cl_of hcl' with rfl | rfl <;> exact absurd hlt (Nat.lt_irrefl _)) rfl
    (var_eval rfl) (fun _ ht => nomatch ht) .top

theorem fnHyp : FnHyp c := by
  refine ⟨fun fn hfn vs hvs => ?_, fun fn hfn ht => ?_, fun fn hfn => ?_, fun fn hfn cl hcl => ?_,
    openDecided_of_readsConfined (by decide +kernel), openLaws_of_plain fun _ h => absurd h List.not_mem_nil⟩
  · obtain rfl := mem_fns hfn
    obtain ⟨v, rfl, hv⟩ := Model.sortsOf_single hvs
    exact ⟨_, eval_B hv⟩
  · obtain rfl := mem_fns hfn
    cases ht
  · obtain rfl := mem_fns hfn
    intro cl cl' h _
    have hm := mem_of_mem_pairs h
    exact ⟨coh (cl_of hm.1) (cl_of hm.2), coh (cl_of hm.2) (cl_of hm.1)⟩
  · obtain rfl := mem_fns hfn
    have h := cl_of hcl
    refine ⟨coh h h, fun hne f fn vs σ _ _ hd => ?_⟩
    rcases h with rfl | rfl
    · have hl := matchA hd.1.2.1
      refine ⟨some va, Or.inr ⟨hne, Or.inl ⟨σ, va, fun _ _ => rfl, sg_sorted hl va_sort, ?_, fun σ'' hag _ => ?_, rfl⟩⟩⟩
      · show EvalTerm c σ (.var 0) (some va) ∧ (∀ t, clA.ens = some t → EvalTerm c σ t (some (bool true))) ∧
          Holds c clA.vars.length σ clA.post true
        exact ⟨var_eval hl, (fun _ ht => nomatch ht), Holds.top⟩
      have hl'' : σ''.lookup 0 = some va := by
        rw [hag 0 (by rw [exsFree_A]; exact List.not_mem_nil), hl]
      exact .gives (var_eval hl'') (fun _ ht => nomatch ht) .top
    · exact absurd rfl hne

set_option maxHeartbeats 1000000 in
/-- Every leaf condition of `coreOK` but `clausesPlain` holds, and `FnHyp`. -/
theorem meets_others : c.subsortsOK = true ∧
    c.fns.all (fun f => f.clauses.all (c.clauseSorted f (c.fns.map Fn.sig))) = true ∧
    c.rules.all c.ruleSorted = true ∧ c.rulesPlain = true ∧ c.paramsPlain = true ∧
    c.faithCoreOK = true ∧ c.hooksApart = true ∧ c.predsApart = true ∧ c.idsOK = true ∧
    c.overloadsOK = true ∧ FnHyp c :=
  ⟨by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap,
    by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, by decide_cheap, fnHyp⟩

theorem not_clausesPlain : c.clausesPlain = false := by decide +kernel

/-- Of what clausesPlain asks of the first clause, only that its existential variable is outside
the left side fails: it is in scope and listed once, its sort is confined, and the clause has no
predicate and no open condition variable. -/
theorem only_left : c.clausePlainEx clA = true ∧ clA.exs.all (· < clA.vars.length) = true ∧
    nodup clA.exs = true ∧ c.condOK clA.vars clA.post = true ∧ clA.pre.isTop = true ∧ clA.reqOpen = false ∧
    clA.exs.all (fun i => !clA.leftVars.contains i) = false ∧ c.clausePlainEx clB = true ∧
    c.clauseExOK clB = true := by
  decide +kernel

/-! ## No model -/

section NoModel

open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

theorem subsorts_trans : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts := by
  have h : (c.subsorts.all fun (a, b) => c.subsorts.all fun (b', d) => b != b' || c.subsorts.contains (a, d)) = true :=
    by decide +kernel
  simp only [List.all_eq_true] at h
  intro a b d hab hbd
  have := h (a, b) hab (b, d) hbd
  simp only [bne_self_eq_false, Bool.false_or, List.contains_iff_mem] at this
  exact this

theorem hfnm : fF ∈ c.allFns := List.mem_append_left _ (List.mem_singleton_self _)
theorem hws : c.sortsOf [va] = some fF.args := by decide +kernel
theorem hpatsA : sortsOfTerms c.patCtxAll clA.vars clA.pats = some fF.args := by decide +kernel
theorem hpatsB : sortsOfTerms c.patCtxAll clB.vars clB.pats = some fF.args := by decide +kernel
theorem hpatsAN : sortsOfTerms c.patCtxNF clA.vars clA.pats = some fF.args := by decide +kernel
theorem hpatsBN : sortsOfTerms c.patCtxNF clB.vars clB.pats = some fF.args := by decide +kernel
theorem hbindsA : ∀ i < clA.vars.length, i ∈ varOccsList clA.pats := by decide +kernel
theorem hbindsB : ∀ i < clB.vars.length, i ∈ varOccsList clB.pats := by decide +kernel

/-- The first clause's equation, as `eqn_atRightEx` reads it. -/
def axA : Kore.Axiom :=
  ⟨[KoreAML.Rv], .implies KoreAML.R (withPre c (canonVars c clA.vars) clA (clausePrem c fF clA))
    (eqConclEx c fF (clauseRightEx c fF clA)), []⟩

theorem hmemA : KoreAML.trAxiom [] [] ⟨0, "kernel", axA⟩ ∈ fnItems c := by
  apply eqn_item_mem hfnm
  rw [axA, ← Model.clauseEquation_axEx (by decide) (by decide)]
  have h : prioEquation c fF clA = clauseEquation c fF clA := by
    unfold prioEquation; rw [show lowerClauses fF clA = [] from rfl]; rfl
  rw [fnEquationsK, show fF.clauses = [clA, clB] from rfl, List.map_cons, h]
  exact List.mem_cons_self ..

theorem hmemB : clauseEquation c fF clB ∈ fnEquationsK c fF := by
  have h : prioEquation c fF clB = clauseEquation c fF clB := by
    unfold prioEquation; rw [show lowerClauses fF clB = [] from rfl]; rfl
  rw [fnEquationsK, show fF.clauses = [clA, clB] from rfl, List.map_cons, List.map_cons, h]
  exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem va_ne_vb : va ≠ vb := by decide

/-- **`Γ c` has no model.** -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ c) := by
  intro M _ I hI
  have hD := defOK hI
  have hnn : NamesNumbered c := namesNumbered_spec (by decide +kernel)
  have hph : patHooksApart c = true := by decide +kernel
  have hg : genWf c = true := by decide +kernel
  have htr := subsorts_trans
  let σ1 : Subst := [(0, va)]
  have hσ1 : c.WellSorted [N] σ1 := sg_sorted rfl va_sort
  let e0 : Valuation M := KoreAML.val0
  -- the second clause: `f(a)` is the element of `a`
  have hmB := hmemB
  rw [clauseEquation_top (cl := clB) rfl rfl] at hmB
  have hvB := premise_vars (c := c) hpatsB hbindsB (fun _ h => by cases h)
  have hB := eqn_at hI hnn lookupF (prem := clausePrem c fF clB) (eqn_item_mem hfnm hmB) hws hσ1
    hvB.1 hvB.2.1 hvB.2.2 (by decide +kernel) (fun _ h => by cases h)
    (r := some va) (fun v hv => by cases hv; exact va_sort)
    (fun tbl e σr m0 _ hag hX hRv hσr2 hm0 =>
      premise_holds4 hI hnn hph htr hfnm hws hσ1 (.cons (.var rfl) .nil) hpatsBN hag hX hRv hσr2 hm0
        (fun _ h => by cases h))
    (fun tbl e hag => right_iff hI hnn hfnm (fun v hv => by cases hv; exact va_sort)
      (fun m => (tr_var 0 m).trans (hag 0 va (by decide) rfl m)) (fun _ h => by cases h)) e0
  -- the first clause: `f(a)` holds the element of `b`
  have hvA := premise_vars (c := c) hpatsA hbindsA (fun _ h => by cases h)
  have hwA : withPre c (canonVars c clA.vars) clA (clausePrem c fF clA) = clausePrem c fF clA := withPre_top rfl
  have hoccA : ∀ i < clA.vars.length, i ∈ clA.exs ∨ i ∈ varOccsList clA.pats ++ clA.condVars ++ varOccs clA.rhs ++
      (clA.ens.map varOccs).getD [] ++ varOccsCond clA.vars.length clA.post := by decide +kernel
  have hVinA := clause_keys_inAxEx (prem := withPre c (canonVars c clA.vars) clA (clausePrem c fF clA))
    hpatsA (fun _ h => by cases h) hoccA (fun _ h => h)
  have hrhsvA : ∀ i ∈ varOccs clA.rhs, i < clA.vars.length := by decide +kernel
  obtain ⟨tbl, e', hk, -, hag, hiff⟩ := eqn_atRightEx hI hnn lookupF hmemA hws hσ1
    (by rw [hwA]; exact hvA.1) hVinA (by rw [hwA]; exact hvA.2.2)
    (fun k hk => freeOf_clauseRightEx hrhsvA (fun _ h => by cases h) (by decide +kernel) hk)
    (fun tbl e σr m0 hk hag hX hRv hσr2 hm0 => by
      rw [hwA]
      exact premise_holds4 hI hnn hph htr hfnm hws hσ1 (.cons (.as (.ctor (by decide +kernel) .nil) rfl) .nil)
        hpatsAN hag hX hRv hσr2 hm0 (fun _ h => by cases h)) e0
  have hkeys : ∀ i < clA.vars.length, canonKey c clA.vars i ∈ tbl := fun i hi => hk _ (hVinA i hi)
  obtain ⟨σr, hσr1, -⟩ := sortSing hI (hnn.2.2 fF hfnm fF.result (List.mem_cons_self ..))
  have hS : ∀ (e : Valuation M) b, (KoreAML.trSort tbl (srtOf c fF.result)).interpret I e b ↔ b = σr := by
    intro e b; unfold srtOf; rw [trSort_srt]; exact hσr1 b
  let m := elemOf c I vb
  have hinB : ∀ e : Valuation M, InS I (c.sortName fF.result) m := fun e =>
    (inS_iff e).mp (elemOf_spec hI vb_sort e).2
  have htop : ∀ e : Valuation M, (KoreAML.tr ⟨tbl, []⟩ (reqPat (srtOf c fF.result) none)).interpret I e m := by
    intro e
    simp only [reqPat]
    rw [KoreAML.tr, KoreAML.interp_sTop hD (by unfold srtOf; rw [trSort_srt]; rfl), KoreAML.interp_inhOf_of (hS e)]
    exact (KoreAML.interp_inhOf_of (S := KoreAML.sym _) (e := e) hσr1).mp ((inS_iff e).mpr (hinB e))
  -- the instance of the first clause's right side at `X = b`
  let x0 := tbl.ev (canonKey c clA.vars 0)
  let e'' : Valuation M := ⟨fun x => if x = x0 then m else e'.evalEvar x, e'.evalSvar⟩
  have hbody : (KoreAML.tr ⟨tbl, []⟩ (clauseRhsBody c fF clA)).interpret I e'' m := by
    unfold clauseRhsBody
    rw [show Cond.conj c (canonVars c clA.vars) (srtOf c fF.result) clA.post = [] from rfl, List.append_nil,
      tr_and2, KoreAML.interp_sAnd]
    refine ⟨?_, htop e''⟩
    rw [show clA.rhs = .var 0 from rfl, tr_var]
    show m = (if tbl.ev (KoreAML.evarKey ((canonVars c clA.vars).getD 0 default).kore) = x0 then m else _)
    rw [if_pos (show tbl.ev (KoreAML.evarKey ((canonVars c clA.vars).getD 0 default).kore) = x0 from rfl)]
  have hright : (KoreAML.tr ⟨tbl, []⟩ (clauseRightEx c fF clA)).interpret I e' m := by
    unfold clauseRightEx
    rw [tr_and2, KoreAML.interp_sAnd]
    refine ⟨existsAll_intro_at hD (clauseExBinders c clA) e' e'' m
      (binders_nodupEx hkeys (by decide) (by decide)) (binders_sortEx (by decide))
      (fun x hx => if_neg (hx _ (List.mem_singleton_self _))) rfl (fun b hb n hn => ?_) hbody, htop e'⟩
    obtain rfl := List.mem_singleton.mp hb
    have hn' : n = c.sortName N := by
      rw [show ((canonVars c clA.vars).getD 0 default).kore.sort = KoreAML.srt (c.sortName N) from
        by rw [canonVars_getD c (by decide)]; rfl] at hn
      exact (srt_inj hn).symm
    subst hn'
    show InS I (c.sortName N) (if tbl.ev (KoreAML.evarKey ((canonVars c clA.vars).getD 0 default).kore) = x0 then m else _)
    rw [if_pos (show tbl.ev (KoreAML.evarKey ((canonVars c clA.vars).getD 0 default).kore) = x0 from rfl)]
    exact hinB e''
  have hA := (hiff m).mpr ⟨hinB e0, hright⟩
  -- the element of `b` is the element of `a`
  have heq : m = elemOf c I va := ((elemOf_spec hI va_sort e0).1 m).mp ((hB m).mp hA)
  exact va_ne_vb (values_apart hI hg htr (by decide +kernel) va_sort vb_sort heq.symm)

end NoModel

/-- **Soundness fails** of `c`, which meets every condition of `coreOK` but `clausesPlain`, and
`FnHyp`. -/
theorem not_sound : ¬ SoundC c := fun h => by
  obtain ⟨⟨M, hM, I, hI⟩, -⟩ := h
  exact no_model M hM I (fun φ hφ => hI φ (Or.inl (Or.inl hφ)))

end ExShadowWitness

end KCore
