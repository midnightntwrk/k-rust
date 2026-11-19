/-
  KCore. A witness that `FnDet` cannot be dropped from `consistent_of`: a semantics with `coreOK`,
  `FnSolves`, `ClausePreDecided`, `ClausePostDecided` (its clauses' right-side predicates are `\top`)
  and `OpenLaws`, without `FnDet`, whose `Γ` has no model. A clause
  of it has a predicate in its premise that is not `\top`; where every clause's predicate is `\top`
  there is no such semantics.

  Two functions over Int:
  - `a(X) => 1` (`aCl1`) and `a(X) => 1 ensures u(X)` (`aCl2`), of one priority;
  - `u(X) => true` where `¬⌈a(X)⌉` (`uCl`), `u : Int → Bool`.
  At an Int `w`:
  - `a(w)` is 1 by `aCl1` (`a_one`);
  - so `¬⌈a(X)⌉` is false at every match (`Holds.not` over `Holds.ceil` at a value), `uCl` fails,
    and `u(w)` is its rest, undefined (`u_none`);
  - so `aCl2`, which decides, has an `ensures` that is not `true`: `a(w)` has no value by
    `Eval.ensFails` (`a_none`);
  - so `¬⌈a(X)⌉` is also true (`Holds.ceil` at the result `none`), `uCl` decides, and `u(w)` is
    `true` (`u_true`).
  `a(w)` has the results 1 and none: `FnDet` fails (`not_fnDet`). `FnSolves` holds (`fnSolves`): it
  speaks of values only; the values of `a` at `w` are 1 alone (`a_res`) and each clause of `a` gives
  1 at its match, the `ensures` `u(X)` having the value `true`; the values of `u` are `true` alone
  (`u_res`). The predicate `¬⌈a(X)⌉` has a truth value wherever `uCl` matches
  (`clausePreDecided`), and `coreOK` accepts the semantics (`coreOK`): `clausesPlain` admits `uCl`,
  whose conditions need no witness.

  `Γ` has no model (`no_model`), so neither has `Γc ∪ Γstep` (`not_consistent`): in a model, a
  function at arguments of its sorts denotes what each of its results denotes (`eval_den4_coreCl`),
  and `a(0)` would denote the element of 1 and nothing. In the sentences: `aCl1`'s states
  `a(x) = 1`; then `uCl`'s premise is false and `u(x)` is its rest, nothing (`ΓFallback`); and
  `aCl2`'s states `a(x) = 1 ∧ ⌈u(x) = true⌉`, which is nothing.
-/
import KcoreSpec.HypWf
import KcoreSpec.SubjectReduction
import KcoreSpec.CoreDecide
import KcoreSpec.Sound
import KcoreSpec.Obligations
import KcoreSpec.OpenClauseFn
import KcoreSpec.PreReadBound
import KcoreSpec.ClausePreFn
import KcoreSpec.ModelUndefRhsWitness

set_option autoImplicit false
set_option maxRecDepth 100000

namespace KCore

namespace FnDetWitness

open Faithful.UndefRhsWitness (cellSorts cellCtors cellSubsorts)

/-- `a` and `u`, numbered after the four cell symbols. -/
def A : Sym := nRegSyms + 4
def Uu : Sym := nRegSyms + 5

def one : GroundTerm := .dv Srt.int (.int 1)
def tt : GroundTerm := .dv Srt.bool (.bool true)

/-- `a(X) => 1`. -/
def aCl1 : Clause := ⟨[Srt.int], [.var 0], none, .dv Srt.int (.int 1), none, 50, false, [], .top, .top⟩
/-- `a(X) => 1 ensures u(X)`. -/
def aCl2 : Clause :=
  ⟨[Srt.int], [.var 0], none, .dv Srt.int (.int 1), some (.app Uu [.var 0]), 50, false, [], .top, .top⟩
def aFn : Fn := ⟨A, [Srt.int], Srt.int, [aCl1, aCl2], false⟩

/-- `¬⌈a(X)⌉`. -/
def preU : Cond := .not (.ceil Srt.int (.app A [.var 0]))

/-- `u(X) => true` where `¬⌈a(X)⌉`. -/
def uCl : Clause := ⟨[Srt.int], [.var 0], none, .dv Srt.bool (.bool true), none, 50, false, [], preU, .top⟩
def uFn : Fn := ⟨Uu, [Srt.int], Srt.bool, [uCl], false⟩

def c : Semantics :=
  { lib := {}
    sortNames := ["KCell", "KCellOpt"]
    symNames := ["LblisKCell", "LblisKCellOpt", "Lbl'-LT-'k'-GT-'", "LblnoKCell", "Lbla", "Lblu"]
    userSorts := cellSorts
    ctors := cellCtors
    fns := [aFn, uFn]
    userSubsorts := cellSubsorts
    pgmSort := Srt.k
    rules := [] }

set_option maxHeartbeats 4000000 in
/-- `coreOK` accepts `c`. -/
theorem coreOK : c.coreOK = true := by decide_coreOK

/-- A clause of `c` has a predicate that is not `\top`. -/
theorem not_preTop : c.clausesPreTop = false := by decide +kernel

theorem lookups : c.lookupFn A = some aFn ∧ c.lookupFn Uu = some uFn := ⟨rfl, rfl⟩

theorem kinds : c.isCtor A = false ∧ isHook A = false ∧ c.isParam A = false ∧ c.isOvl A = false ∧
    c.isCtor Uu = false ∧ isHook Uu = false ∧ c.isParam Uu = false ∧ c.isOvl Uu = false := by decide +kernel

theorem aCl_of {cl : Clause} (h : cl ∈ aFn.clauses) : cl = aCl1 ∨ cl = aCl2 := by simpa [aFn] using h
theorem uCl_of {cl : Clause} (h : cl ∈ uFn.clauses) : cl = uCl := by simpa [uFn] using h
theorem mem_fns {fn : Fn} (h : fn ∈ c.fns) : fn = aFn ∨ fn = uFn := by simpa [c] using h

/-! ## Matches -/

theorem match0 {σ : Subst} {vs : List GroundTerm} (h : PatVals c σ [.var 0] vs) :
    ∃ v, vs = [v] ∧ σ.lookup 0 = some v := by
  obtain ⟨v, vs', rfl, hv, hs⟩ := PatVals.cons_inv h
  rw [PatVals.nil_inv hs]
  exact ⟨v, rfl, PatVal.var_inv hv⟩

/-- The substitution that gives the one variable the value `v`. -/
def sg (v : GroundTerm) : Subst := [(0, v)]

theorem sg_sortedAt {v : GroundTerm} (hv : c.sortOf v = some Srt.int) (is : List Nat) :
    c.WellSortedAt [Srt.int] is (sg v) := by
  intro i _ s hs
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨v, rfl, hv⟩
  | succ i => simp at hs

theorem sg_sorted {v : GroundTerm} (hv : c.sortOf v = some Srt.int) : c.WellSorted [Srt.int] (sg v) := by
  intro i s hs
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨v, rfl, hv⟩
  | succ i => simp at hs

theorem sg_match (v : GroundTerm) : PatVals c (sg v) [.var 0] [v] := .cons (.var rfl) .nil

theorem allSome1 (a : GroundTerm) : allSome [some a] = some [a] := rfl

/-- A call of `f` at the variable X, where X is `w`, has `f`'s result at `w`. -/
theorem call_mk {f : Sym} (hk : c.isCtor f = false) (hh : isHook f = false) (hp : c.isParam f = false)
    {σ : Subst} {w : GroundTerm} (hl : σ.lookup 0 = some w) {r : Option GroundTerm} (h : Eval c f [w] r) :
    EvalTerm c σ (.app f [.var 0]) r :=
  .call (vs := [w]) hk hh (.cons .var .nil) (by rw [hl]; rfl) h hp

/-- A result of such a call is a result of `f` at `w`. -/
theorem call_inv {f : Sym} (hk : c.isCtor f = false) (hh : isHook f = false) (hp : c.isParam f = false)
    (ho : c.isOvl f = false)
    {σ : Subst} {w : GroundTerm} (hl : σ.lookup 0 = some w) {r : Option GroundTerm}
    (h : EvalTerm c σ (.app f [.var 0]) r) : Eval c f [w] r := by
  cases h with
  | ctor hk' _ => exact absurd (hk.symm.trans hk') (by simp)
  | hook _ hhk _ _ _ => exact absurd (hh.symm.trans hhk) (by simp)
  | param _ _ hp' _ _ => exact absurd (hp.symm.trans hp') (by simp)
  | call _ _ hts hvs hf _ =>
    cases hts with
    | cons h1 hs =>
      cases hs; cases h1
      rw [hl] at hvs
      obtain rfl := Option.some.inj (hvs.symm.trans (allSome1 _))
      exact hf
  | callUndef _ _ hts hvs _ =>
    cases hts with
    | cons h1 hs =>
      cases hs; cases h1
      rw [hl] at hvs
      exact absurd (hvs.symm.trans (allSome1 _)) (by simp)
  | ovl _ ho' _ _ => exact absurd (ho.symm.trans ho') (by simp)
  | ovlFn _ ho' _ _ _ _ _ => exact absurd (ho.symm.trans ho') (by simp)

/-! ## The four results -/

section Results

variable {w : GroundTerm} (hw : c.sortOf w = some Srt.int)
include hw

omit hw in
/-- No clause of `a` is of a smaller priority than another. -/
theorem a_prio {cl : Clause} (hcl : cl ∈ aFn.clauses) :
    ∀ cl' ∈ aFn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails c [w] cl' := by
  intro cl' hcl' _ hlt
  rcases aCl_of hcl with rfl | rfl <;> rcases aCl_of hcl' with rfl | rfl <;> exact absurd hlt (Nat.lt_irrefl _)

/-- **`a(w)` is 1**, by its first clause. -/
theorem a_one : Eval c A [w] (some one) :=
  .clause (fn := aFn) (cl := aCl1) (σ := sg w) lookups.1 (List.mem_cons_self ..) (sg_sorted hw) (sg_match _)
    (fun _ ht => nomatch ht) .top (a_prio (List.mem_cons_self ..)) rfl .dv (fun _ ht => nomatch ht) .top

/-- `¬⌈a(X)⌉` is false where X is `w`: `a(w)` has a value. -/
theorem pre_false {σ : Subst} (hl : σ.lookup 0 = some w) : Holds c 1 σ preU false :=
  .not (.ceil (call_mk kinds.1 kinds.2.1 kinds.2.2.1 hl (a_one hw)))

/-- `u`'s clause fails at `w`. -/
theorem u_fails : Fails c [w] uCl :=
  .intro fun σ _ hm => by
    obtain ⟨v, hv, hl⟩ := match0 hm
    cases hv
    exact .pre (pre_false hw hl)

/-- **`u(w)` is undefined**: its clause fails, and it has no rest. -/
theorem u_none : Eval c Uu [w] none :=
  .rest (fn := uFn) lookups.2 fun cl hcl => by rw [uCl_of hcl]; exact u_fails hw

/-- **`a(w)` has no value**, by its second clause, whose `ensures` `u(X)` is not `true`. -/
theorem a_none : Eval c A [w] none :=
  .ensFails (fn := aFn) (cl := aCl2) (σ := sg w) (w := none) lookups.1
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (sg_sorted hw) (sg_match _)
    (fun _ ht => nomatch ht) .top (a_prio (List.mem_cons_of_mem _ (List.mem_singleton_self _))) rfl rfl
    (call_mk kinds.2.2.2.2.1 kinds.2.2.2.2.2.1 kinds.2.2.2.2.2.2.1 rfl (u_none hw)) (by intro h; cases h)

/-- `¬⌈a(X)⌉` is true where X is `w`: `a(w)` has the result none. -/
theorem pre_true {σ : Subst} (hl : σ.lookup 0 = some w) : Holds c 1 σ preU true :=
  .not (.ceil (call_mk kinds.1 kinds.2.1 kinds.2.2.1 hl (a_none hw)))

/-- **`u(w)` is `true`**: its clause decides. -/
theorem u_true : Eval c Uu [w] (some tt) :=
  .clause (fn := uFn) (cl := uCl) (σ := sg w) lookups.2 (List.mem_singleton_self _) (sg_sorted hw) (sg_match _)
    (fun _ ht => nomatch ht) (pre_true hw rfl)
    (fun cl' hcl' _ hlt => by rw [uCl_of hcl'] at hlt; exact absurd hlt (Nat.lt_irrefl _))
    rfl .dv (fun _ ht => nomatch ht) .top

end Results

/-- `a` has no result but 1 and none. -/
theorem a_res {w : GroundTerm} (hw : c.sortOf w = some Srt.int) {r : Option GroundTerm} (h : Eval c A [w] r) :
    r = some one ∨ r = none := by
  cases h with
  | clause hfn hcl _ _ _ _ _ _ hrhs _ _ =>
    obtain rfl := Option.some.inj (lookups.1.symm.trans hfn)
    rcases aCl_of hcl with rfl | rfl <;> exact .inl (EvalTerm.dv_inv hrhs)
  | rest hfn hnone =>
    obtain rfl := Option.some.inj (lookups.1.symm.trans hfn)
    cases hnone aCl1 (List.mem_cons_self ..) with
    | intro h =>
      cases h (sg w) (sg_sortedAt hw _) (sg_match _) with
      | intro ht _ _ => cases ht
      | pre hp => exact absurd hp.top_eq (by simp)
  | ensFails => exact .inr rfl
  | clauseEx hfn hcl _ _ _ _ _ hne _ _ _ _ =>
    obtain rfl := Option.some.inj (lookups.1.symm.trans hfn)
    rcases aCl_of hcl with rfl | rfl <;> exact absurd rfl hne
  | exNone => exact .inr rfl

/-- `u` has no result but `true` and none. -/
theorem u_res {w : GroundTerm} {r : Option GroundTerm} (h : Eval c Uu [w] r) : r = some tt ∨ r = none := by
  cases h with
  | clause hfn hcl _ _ _ _ _ _ hrhs _ _ =>
    obtain rfl := Option.some.inj (lookups.2.symm.trans hfn)
    obtain rfl := uCl_of hcl
    exact .inl (EvalTerm.dv_inv hrhs)
  | rest hfn hnone =>
    obtain rfl := Option.some.inj (lookups.2.symm.trans hfn)
    exact .inr rfl
  | ensFails => exact .inr rfl
  | clauseEx hfn hcl _ _ _ _ _ hne _ _ _ _ =>
    obtain rfl := Option.some.inj (lookups.2.symm.trans hfn)
    obtain rfl := uCl_of hcl
    exact absurd rfl hne
  | exNone => exact .inr rfl

/-! ## The hypotheses -/

theorem i0_int : c.sortOf (.dv Srt.int (.int 0)) = some Srt.int := by decide +kernel

/-- **Not `FnDet`**: `a(0)` has the results 1 and none. -/
theorem not_fnDet : ¬ FnDet c := fun hd => by
  have := hd _ _ _ _ (a_one i0_int) (a_none i0_int)
  cases this

/-- What a clause of `c` that applies gives: X is an Int `w`, and the argument list is `[w]`. -/
theorem applies_int {cl : Clause} (hv : cl.vars = [Srt.int]) (hp : cl.pats = [.var 0]) (hex : cl.exs = [])
    {σ : Subst} {vs : List GroundTerm} (ha : cl.AppliesAt c σ vs) :
    ∃ w, σ.lookup 0 = some w ∧ c.sortOf w = some Srt.int ∧ vs = [w] ∧ c.WellSorted cl.vars σ := by
  have hσ := (wellSortedAt_univ hex).mp ha.1
  have hm := ha.2.1
  rw [hp] at hm
  obtain ⟨w', rfl, hl'⟩ := match0 hm
  obtain ⟨w, hl, hw⟩ := hσ 0 Srt.int (by rw [hv]; rfl)
  rw [hl] at hl'; cases hl'
  exact ⟨_, hl, hw, rfl, hσ⟩

/-- **Evaluation solves the equations of `c`**: the values of `a` at an Int are 1 alone, which each
of its clauses gives at its match, `u(X)` having the value `true`; the values of `u` are `true`
alone, which its clause gives. -/
theorem fnSolves : FnSolves c := by
  intro fn hfn vs _ cl hcl σ hdec v
  rcases mem_fns hfn with rfl | rfl
  · rcases aCl_of hcl with rfl | rfl
    · obtain ⟨w, hl, hw, rfl, hσ⟩ := applies_int rfl rfl rfl hdec.1
      refine Iff.trans ?_ (Clause.gives_iff_noExs (cl := aCl1) rfl rfl hσ v).symm
      constructor
      · intro h
        rcases a_res hw h with h1 | h1
        · cases h1; exact ⟨.dv, fun _ ht => nomatch ht⟩
        · cases h1
      · rintro ⟨hr, -⟩
        cases (EvalTerm.dv_inv hr : some v = some one)
        exact a_one hw
    · obtain ⟨w, hl, hw, rfl, hσ⟩ := applies_int rfl rfl rfl hdec.1
      refine Iff.trans ?_ (Clause.gives_iff_noExs (cl := aCl2) rfl rfl hσ v).symm
      constructor
      · intro h
        rcases a_res hw h with h1 | h1
        · cases h1
          exact ⟨.dv, fun t ht => by
            cases ht
            exact call_mk kinds.2.2.2.2.1 kinds.2.2.2.2.2.1 kinds.2.2.2.2.2.2.1 hl (u_true hw)⟩
        · cases h1
      · rintro ⟨hr, -⟩
        cases (EvalTerm.dv_inv hr : some v = some one)
        exact a_one hw
  · obtain rfl := uCl_of hcl
    obtain ⟨w, hl, hw, rfl, hσ⟩ := applies_int rfl rfl rfl hdec.1
    refine Iff.trans ?_ (Clause.gives_iff_noExs (cl := uCl) rfl rfl hσ v).symm
    constructor
    · intro h
      rcases u_res h with h1 | h1
      · cases h1; exact ⟨.dv, fun _ ht => nomatch ht⟩
      · cases h1
    · rintro ⟨hr, -⟩
      cases (EvalTerm.dv_inv hr : some v = some tt)
      exact u_true hw

/-- **Each clause's predicate has a truth value where its patterns match**: `¬⌈a(X)⌉` is false
there (and true). -/
theorem clausePreDecided : ClausePreDecided c := by
  intro fn hfn cl hcl σ vs hσ hm
  rcases mem_fns hfn with rfl | rfl
  · rcases aCl_of hcl with rfl | rfl <;> exact ⟨true, .top⟩
  · obtain rfl := uCl_of hcl
    obtain ⟨w, hl, hw⟩ := hσ 0 (by decide) Srt.int rfl
    exact ⟨false, pre_false hw hl⟩

/-- `OpenLaws`, from `coreOK`. -/
theorem openLaws : OpenLaws c := openLaws_of_plain (by decide +kernel)

/-- `ClausePostDecided`: every clause's right-side predicate is `\top`. -/
theorem clausePostDecided : ClausePostDecided c := clausePostDecided_of_isTop (by decide +kernel)

/-! ## `Γ` has no model -/

section NoModel

open ML Faithful

/-- No clause of `c` has conditions that need a witness. -/
theorem noWitness : ∀ fn ∈ c.fns, ∀ cl ∈ fn.clauses, cl.needsWitness c = true → cl.CondDecided c := by
  intro fn hfn cl hcl h
  have h0 : c.fns.all (fun f => f.clauses.all fun cl => !cl.needsWitness c) = true := by decide +kernel
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp h0 fn hfn) cl hcl
  rw [h] at h1; cases h1

/-- **`Γc` has no model**: `a(0)` would denote the element of 1, its result by the first clause,
and nothing, its result by the second. -/
theorem no_model_c : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γc c) := by
  intro M _ I hIc
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core coreOK
  haveI : OvlOK c := hno
  have hI : I ⊧ᴵP Γ c := fun φ hφ => hIc φ (Or.inl hφ)
  have hden := fun (r : Option GroundTerm) (hev : Eval c A [.dv Srt.int (.int 0)] r) (e : Valuation M) (m : M) =>
    eval_den4_coreCl hIc (by decide +kernel : c.sortedOKCl = true) hsr (Semantics.coreOK_parts coreOK).2.1 hph
      noWitness (HoldsShape.preReadAll_of_core coreOK hIc) hev lookups.1 (by decide +kernel) e m
  let e : Valuation M := ⟨fun _ => default, fun _ _ => False⟩
  obtain ⟨hone, -⟩ := elemOf_spec hI (v := one) (s := Srt.int) (by decide +kernel) e
  have h1 := (hden _ (a_one i0_int) e (elemOf c I one)).mpr ((hone _).mpr rfl)
  exact (hden _ (a_none i0_int) e (elemOf c I one)).mp h1

/-- **`Γ` has no model**: `c` reads no confined sort, so `Γc` is `Γ`. -/
theorem no_model : ∀ (M : Type) (_ : Inhabited M) (I : Interpretation KoreAML.Sym M), ¬ (I ⊧ᴵP Γ c) := by
  intro M hM I hI
  refine no_model_c M hM I ?_
  rw [Γc_plain (by decide +kernel)]; exact hI

/-- **Not `Consistent`**: `Γc` is part of `Γc ∪ Γstep`. -/
theorem not_consistent : ¬ Consistent c := fun ⟨M, hM, I, hI⟩ =>
  no_model_c M hM I (fun φ hφ => hI φ (Or.inl hφ))

end NoModel

end FnDetWitness

end KCore
