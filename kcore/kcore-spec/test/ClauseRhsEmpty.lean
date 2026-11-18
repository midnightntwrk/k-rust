/-
  Function equations with a right-side variable of a sort without a value, through the reader, on
  K 7.1.337 kompile's own texts. Run from the package root:
  `lake env lean -j1 test/ClauseRhsEmpty.lean`. Kernel-checked (`decide +kernel`) where a fact is
  about the semantics.

  - `Peer` (fixture e2-clause-rhs-empty-peer, `f2-examples/rhsemptypeer.kompile.kore`):
    `rule f() => g(Y:Empty) [unboundVariables(Y)]` beside `rule f() => a`, of one priority. The
    reader's `f` has the clauses `f() => a` (index 0) and `f() => g(Y)` (index 1, Y of Empty). The
    semantics is `coreOK`; `f` is held-named (`Semantics.heldObligations`), named for agreement
    (`agreeObligationsI`) and its clause 1 for match independence (`matchObligationsL`). No value
    has sort Empty (`noValue`), so clause 1 applies under no substitution (`clY_not_applies`): the
    owed facts hold, `f` by the second of `HeldOwed`'s facts (`f()` is `a` by clause 0, and `f` is
    not `[total]`), `ClausesAgree` and `MatchIndependent` because clause 1 applies nowhere.
    `FnHyp` follows from the held-named form (`fnHyp_of_fnObligationsN`), and with it the pinned
    `sound_hyp` and `exact_hyp`; `f()` is `a` and has no other result (`f_is_a`).
  - `Owise` (fixture e2-clause-rhs-empty-owise, `f2-examples/rhsemptyowise.kompile.kore`):
    `rule f(0) => g(Y:Empty) [unboundVariables(Y)]` beside `rule f(_) => a [owise]`. The reader's
    `f` has `f(0) => g(Y)` (index 0, priority 50) and `f(X) => a` (index 1, priority 200). The
    semantics is `coreOK` and `f` is held-named. The clause of priority 50 is excluded by its
    pattern alone, Y outside it (`Fails` ranges over substitutions of the pattern's variables):
    `f(1)` is `a` (`f1_is_a`). At 0 the clause of priority 50 neither applies (Y has no value) nor
    fails (its pattern matches and it has no condition), so `f(0)` has no result (`f0_none`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore

namespace ClauseRhsEmpty

/-- **No value has the sort `e`** when no constructor, overload, open generator or subsort ends
there, no literal is of it and it is no collection sort. -/
theorem noValue {c : Semantics} {e : Srt} (hctor : c.ctorSigs.all (·.result != e) = true)
    (hovl : c.ovls = []) (hraw : ∀ k ∈ c.params, k.raw = false)
    (hsub : c.subsorts.all (fun p => p.2 != e) = true) (hcoll : c.collOf e = none)
    (hcarr : c.lib.carriers.all (·.1 != e) = true)
    (hlit : (e != Srt.int && e != Srt.bool && e != Srt.kconfigVar && e != Srt.string && e != Srt.bytes &&
      e != Srt.float && !c.lib.tokenSorts.contains e && !c.lib.byteSorts.contains e) = true)
    (v : GroundTerm) : c.sortOf v ≠ some e := by
  intro h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hlit
  obtain ⟨⟨⟨⟨⟨⟨⟨hi, hb⟩, hk⟩, hs⟩, hy⟩, hf⟩, ht⟩, hbs⟩ := hlit
  cases v with
  | ctor f ts =>
    rw [Semantics.sortOf] at h
    cases hk' : lookupSig c.ctorSigs f with
    | none =>
      have : c.lookupOvl f = none := by simp [Semantics.lookupOvl, hovl]
      rw [hk', this, c.lookupOpen_of_noRaw hraw f] at h; cases h
    | some k =>
      rw [hk'] at h
      simp only at h
      split at h
      · have hm := List.mem_of_find?_eq_some (by rw [← lookupSig_eq]; exact hk')
        have := List.all_eq_true.mp hctor k hm
        rw [Option.some.inj h] at this
        simp at this
      · cases h
  | inj a b t =>
    rw [Semantics.sortOf] at h
    split at h
    · rename_i h'
      cases h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h'
      have := List.all_eq_true.mp hsub _ h'.1.1
      simp at this
    · cases h
  | dv s' lit =>
    obtain ⟨hd, rfl⟩ := sortOf_dv.mp h
    have hcs := Lib.carrier_of_not _ hcarr
    cases lit with
    | int _ => simp only [dvOK, hcs, beq_iff_eq] at hd; exact hi hd
    | bool _ => simp only [dvOK, hcs, beq_iff_eq] at hd; exact hb hd
    | float _ _ _ => simp only [dvOK, hcs, Bool.and_eq_true, beq_iff_eq] at hd; exact hf hd.1
    | tok t =>
      simp only [dvOK, hcs, ht, hbs, Bool.or_false, Bool.and_eq_true, Bool.or_eq_true,
        beq_iff_eq] at hd
      rcases hd with (hd | hd) | ⟨hd, -⟩
      · exact hk hd
      · exact hs hd
      · exact hy hd
  | map s' es =>
    obtain ⟨k, -, hco, -, -, -, -, rfl⟩ := sortOf_mapS_fwd h
    rw [hcoll] at hco; cases hco
  | set s' es =>
    obtain ⟨k, hco, -, -, -, rfl⟩ := sortOf_setS.mp h
    rw [hcoll] at hco; cases hco
  | list s' es =>
    obtain ⟨k, hco, -, -, rfl⟩ := sortOf_listS.mp h
    rw [hcoll] at hco; cases hco

theorem sortsOf_nil {c : Semantics} {vs : List GroundTerm} (h : c.sortsOf vs = some []) : vs = [] := by
  cases vs with
  | nil => rfl
  | cons v vs => simp only [Semantics.sortsOf] at h; split at h <;> cases h

/-- A constant constructor evaluates to itself. -/
theorem evalConst {c : Semantics} {σ : Subst} {f : Sym} (h : c.isCtor f = true) :
    EvalTerm c σ (.app f []) (some (.ctor f [])) :=
  EvalTerm.ctor (rs := []) h .nil

/-! ## e2-clause-rhs-empty-peer -/

namespace Peer

definition_of defn from "f2-examples/rhsemptypeer.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

/-- The symbols and the sort the clauses name. -/
example : c.symName 388 = "Lblf" ∧ c.symName 386 = "Lbla" ∧ c.symName 387 = "Lblg" ∧
    c.sortName 33 = "Empty" := by
  decide +kernel

/-- A rank of the user's functions: `f` alone. -/
def ord : List Sym := [388]

/-- The semantics is `coreOK`, `rightValued` fails and `f` is the one held-named function; the
lists the package would state: no function named for termination or totality, `f` for agreement,
its clause 1 for match independence, no rule and no clause owing a condition. -/
theorem named : c.coreOK = true ∧ c.rightValued = false ∧ c.heldObligations = [388] ∧
    c.rankObligations ord ++ c.decObligationsL = [] ∧ c.totalObligationsRP ord [] = [] ∧
    c.agreeObligationsI = [388] ∧ c.matchObligationsL = [(388, 1)] ∧ c.owedRules = [] ∧
    c.owedClauses = [] := by
  decide_cheap

theorem core : c.coreOK = true := named.1

/-- What `noValue` asks of Empty (33). -/
theorem empty : c.ctorSigs.all (·.result != 33) = true ∧ c.ovls = [] ∧ c.params.all (!·.raw) = true ∧
    c.subsorts.all (fun p => p.2 != 33) = true ∧ c.collOf 33 = none ∧ c.lib.carriers.all (·.1 != 33) = true ∧
    ((33 : Srt) != Srt.int && (33 : Srt) != Srt.bool && (33 : Srt) != Srt.kconfigVar && (33 : Srt) != Srt.string &&
      (33 : Srt) != Srt.bytes && (33 : Srt) != Srt.float && !c.lib.tokenSorts.contains 33 &&
      !c.lib.byteSorts.contains 33) = true := by
  decide +kernel

theorem noRaw : ∀ k ∈ c.params, k.raw = false := fun k hk => by
  have := List.all_eq_true.mp empty.2.2.1 k hk; simpa using this

/-- **No value has sort Empty.** -/
theorem no_E (v : GroundTerm) : c.sortOf v ≠ some 33 :=
  noValue empty.1 empty.2.1 noRaw empty.2.2.2.1 empty.2.2.2.2.1 empty.2.2.2.2.2.1 empty.2.2.2.2.2.2 v

/-- The reader's `f` and its two clauses. -/
noncomputable def fF : Fn := c.fns[0]'(by decide +kernel)
noncomputable def clA : Clause := fF.clauses[0]'(by decide +kernel)
noncomputable def clY : Clause := fF.clauses[1]'(by decide +kernel)

theorem fF_mem : fF ∈ c.fns := List.getElem_mem _

/-- `f() => a` and `f() => g(Y:Empty)`, of one priority, neither `aside`; `f` is not `[total]`. -/
theorem fF_shape : fF.label = 388 ∧ fF.args = [] ∧ fF.total = false ∧ fF.clauses.length = 2 ∧
    clA.vars = [] ∧ clA.pats.isEmpty = true ∧ clA.req.isNone = true ∧ clA.ens.isNone = true ∧
    clY.vars = [33] ∧ clY.leftVars = [] ∧ clA.prio = clY.prio ∧ c.isCtor 386 = true := by
  decide +kernel

theorem clA_rhs : clA.rhs = .app 386 [] := by rfl
theorem clY_vars : clY.vars = [33] := fF_shape.2.2.2.2.2.2.2.2.1
theorem clY_left : clY.leftVars = [] := fF_shape.2.2.2.2.2.2.2.2.2.1
theorem clA_pre : clA.pre = .top := by rfl

theorem clauses_eq : fF.clauses = [clA, clY] := by
  apply List.ext_getElem (by rw [fF_shape.2.2.2.1]; rfl)
  intro i h1 _
  have : i < 2 := fF_shape.2.2.2.1 ▸ h1
  match i, this with
  | 0, _ => rfl
  | 1, _ => rfl

theorem lookupF : c.lookupFn 388 = some fF := fF_shape.1 ▸ lookupFn_of_core core fF_mem

theorem lookupF_eq {fn : Fn} (h : c.lookupFn 388 = some fn) : fn = fF :=
  Option.some.inj (h.symm.trans lookupF)

/-- `f() => g(Y:Empty)` applies under no substitution: Y is of Empty. -/
theorem clY_not_applies (σ : Subst) (vs : List GroundTerm) : ¬ clY.AppliesAt c σ vs := by
  rintro ⟨h, -⟩
  obtain ⟨v, -, hv⟩ := h 0 33 (by rw [clY_vars]; rfl)
  exact no_E v hv

/-- **`f()` is `a`**, by `f() => a`; the other clause is of the same priority. -/
theorem evalF : Eval c 388 [] (some (.ctor 386 [])) := by
  obtain ⟨-, -, -, -, hva, hpa, hra, hea, -, -, hprio, hctor⟩ := fF_shape
  refine Eval.clause (cl := clA) (σ := []) lookupF (by rw [clauses_eq]; exact List.mem_cons_self)
    (fun i s h => by rw [hva] at h; cases h) (by rw [List.isEmpty_iff.mp hpa]; exact .nil)
    (fun t h => by rw [h] at hra; cases hra) (by rw [clA_pre]; exact .top) (fun cl' h _ hlt => ?_)
    (by rfl) (by rw [clA_rhs]; exact evalConst hctor) (fun t h => by rw [h] at hea; cases hea)
    (Clause.holds_postTop (by rfl) _)
  rw [clauses_eq] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact absurd hlt (Nat.lt_irrefl _)
  · rw [hprio] at hlt; exact absurd hlt (Nat.lt_irrefl _)

/-- **`f` terminates**: its one argument list is `[]`, where `f()` is `a`. -/
theorem terminatesF : Terminates c 388 := fun fn hfn vs hvs => by
  have e := lookupF_eq hfn
  subst e
  rw [fF_shape.2.1] at hvs
  rw [sortsOf_nil hvs]
  exact ⟨_, evalF⟩

/-- **What is owed of `f`, by the second fact**: `f()` is `a`, and `f` is not `[total]`. The first
fact is false: Y is of Empty. -/
theorem held : ∀ f ∈ c.heldObligations, HeldOwed c f := by
  intro f hf fn hfn
  rw [named.2.2.1, List.mem_singleton] at hf
  subst hf
  have e := lookupF_eq hfn
  subst e
  exact .inr ⟨terminatesF, fun ht => by rw [fF_shape.2.2.1] at ht; cases ht⟩

theorem not_heldFn : ¬ c.HeldFn fF := fun h => by
  rcases h clY (by rw [clauses_eq]; simp) 0 33 (by rw [clY_vars]; rfl) with h | ⟨v, hv⟩
  · rw [clY_left] at h; cases h
  · exact no_E v hv

/-- **`f`'s equations agree**: `f() => g(Y)` applies nowhere. -/
theorem agree : ClausesAgree c fF := by
  intro cl cl' hp _
  have hp' : (cl, cl') = (clA, clY) := by rw [clauses_eq] at hp; simpa [pairs] using hp
  cases hp'
  exact ⟨fun vs _ σ' _ ha => absurd ha (clY_not_applies σ' vs), fun vs σ _ ha => absurd ha (clY_not_applies σ vs)⟩

/-- **`f() => g(Y)` is match independent**: it applies nowhere. -/
theorem matchY : MatchIndependent c clY :=
  (matchIndependent_iff_noExs (by rfl)).mpr fun vs σ _ ha => absurd ha (clY_not_applies σ vs)

/-- **The facts the deciders leave of `FnHyp`**: the two named ones. -/
theorem obl : FnObligations c ord [] := by
  obtain ⟨-, -, -, hterm, htot, hagr, hmat, howR, howC⟩ := named
  refine ⟨fun f hf => (by rw [hterm] at hf; cases hf), fun f hf => (by rw [htot] at hf; cases hf),
    fun f hf fn hfn => ?_, fun p hp fn hfn cl hcl => ?_,
    ⟨openRules_of_owed (by rw [howR]; intro i hi; cases hi),
     openClauses_of_owed (by rw [howC]; intro p hp; cases hp)⟩,
    openLaws_of_plain noRaw⟩
  · rw [hagr, List.mem_singleton] at hf
    subst hf
    have e := lookupF_eq hfn
    subst e
    exact agree
  · rw [hmat, List.mem_singleton] at hp
    subst hp
    have e := lookupF_eq hfn
    subst e
    rw [clauses_eq] at hcl
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hcl
    subst hcl
    exact matchY

/-- **`FnHyp` from the held-named form**: `coreOK`, the owed fact of `f` and the deciders. -/
theorem fnHyp : FnHyp c := fnHyp_of_fnObligationsN core held ParamsTotal.nil obl

/-- **`f()` is `a`, and nothing else.** -/
theorem f_is_a : Eval c 388 [] (some (.ctor 386 [])) ∧ ∀ r, Eval c 388 [] r → r = some (.ctor 386 []) :=
  ⟨evalF, fun _ h => (fnModel_of_fnHyp core fnHyp).1 _ _ _ _ h evalF⟩

/-- The pinned statements at the reader's semantics. -/
example : SoundC c := sound_hyp c core fnHyp
example : ExactC c := exact_hyp c core fnHyp
example : SoundC c := sound_fnN c ord [] core held ParamsTotal.nil obl

/--
info: 'ClauseRhsEmpty.Peer.fnHyp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms fnHyp

end Peer

/-! ## e2-clause-rhs-empty-owise -/

namespace Owise

definition_of defn from "f2-examples/rhsemptyowise.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

example : c.symName 388 = "Lblf" ∧ c.symName 386 = "Lbla" ∧ c.symName 387 = "Lblg" ∧
    c.sortName 33 = "Empty" := by
  decide +kernel

/-- `coreOK`; `f` is the one held-named function; its clause 0 is named for match independence. -/
theorem named : c.coreOK = true ∧ c.rightValued = false ∧ c.heldObligations = [388] ∧
    c.agreeObligationsI = [] ∧ c.matchObligationsL = [(388, 0)] := by
  decide_cheap

theorem core : c.coreOK = true := named.1

theorem empty : c.ctorSigs.all (·.result != 33) = true ∧ c.ovls = [] ∧ c.params.all (!·.raw) = true ∧
    c.subsorts.all (fun p => p.2 != 33) = true ∧ c.collOf 33 = none ∧ c.lib.carriers.all (·.1 != 33) = true ∧
    ((33 : Srt) != Srt.int && (33 : Srt) != Srt.bool && (33 : Srt) != Srt.kconfigVar && (33 : Srt) != Srt.string &&
      (33 : Srt) != Srt.bytes && (33 : Srt) != Srt.float && !c.lib.tokenSorts.contains 33 &&
      !c.lib.byteSorts.contains 33) = true := by
  decide +kernel

theorem noRaw : ∀ k ∈ c.params, k.raw = false := fun k hk => by
  have := List.all_eq_true.mp empty.2.2.1 k hk; simpa using this

theorem no_E (v : GroundTerm) : c.sortOf v ≠ some 33 :=
  noValue empty.1 empty.2.1 noRaw empty.2.2.2.1 empty.2.2.2.2.1 empty.2.2.2.2.2.1 empty.2.2.2.2.2.2 v

noncomputable def fF : Fn := c.fns[0]'(by decide +kernel)
noncomputable def cl0 : Clause := fF.clauses[0]'(by decide +kernel)
noncomputable def clX : Clause := fF.clauses[1]'(by decide +kernel)

theorem fF_mem : fF ∈ c.fns := List.getElem_mem _

/-- `f(0) => g(Y:Empty)` at priority 50 and `f(X) => a` at priority 200 (the `[owise]` one). -/
theorem fF_shape : fF.label = 388 ∧ fF.clauses.length = 2 ∧
    cl0.vars = [33] ∧ cl0.req.isNone = true ∧ cl0.ens.isNone = true ∧ cl0.aside = false ∧ cl0.prio = 50 ∧
    clX.vars = [Srt.int] ∧ clX.req.isNone = true ∧ clX.ens.isNone = true ∧ clX.aside = false ∧
    clX.prio = 200 ∧ c.isCtor 386 = true ∧ cl0.leftVars = [] := by
  decide +kernel

theorem cl0_pats : cl0.pats = [.dv Srt.int (.int 0)] := by rfl
theorem cl0_pre : cl0.pre = .top := by rfl
theorem clX_pats : clX.pats = [.var 0] := by rfl
theorem clX_rhs : clX.rhs = .app 386 [] := by rfl
theorem clX_pre : clX.pre = .top := by rfl

theorem clauses_eq : fF.clauses = [cl0, clX] := by
  apply List.ext_getElem (by rw [fF_shape.2.1]; rfl)
  intro i h1 _
  have : i < 2 := fF_shape.2.1 ▸ h1
  match i, this with
  | 0, _ => rfl
  | 1, _ => rfl

theorem lookupF : c.lookupFn 388 = some fF := fF_shape.1 ▸ lookupFn_of_core core fF_mem

theorem lookupF_eq {fn : Fn} (h : c.lookupFn 388 = some fn) : fn = fF :=
  Option.some.inj (h.symm.trans lookupF)

def one : GroundTerm := .dv Srt.int (.int 1)
def zero : GroundTerm := .dv Srt.int (.int 0)

theorem sortOf_one : c.sortOf one = some Srt.int :=
  sortOf_dv.mpr ⟨by decide +kernel, rfl⟩

/-- **`f(0) => g(Y)` fails at 1**: its pattern does not denote 1, whatever Y is. -/
theorem cl0_fails_one : Fails c [one] cl0 :=
  .intro fun σ _ hm => by
    rw [cl0_pats] at hm
    cases hm with
    | cons h _ => cases h

/-- **`f(1)` is `a`**, by the `[owise]` clause: the clause of priority 50 fails at 1. -/
theorem f1_is_a : Eval c 388 [one] (some (.ctor 386 [])) := by
  obtain ⟨-, -, -, -, -, -, -, hvx, hrx, hex, -, hpx', hctor, -⟩ := fF_shape
  refine Eval.clause (cl := clX) (σ := [(0, one)]) lookupF (by rw [clauses_eq]; simp)
    (fun i s h => ?_) (by rw [clX_pats]; exact .cons (.var rfl) .nil) (fun t h => by rw [h] at hrx; cases hrx)
    (by rw [clX_pre]; exact .top) (fun cl' h ha hlt => ?_) (by rfl) (by rw [clX_rhs]; exact evalConst hctor)
    (fun t h => by rw [h] at hex; cases hex) (Clause.holds_postTop (by rfl) _)
  · rw [hvx] at h
    cases i with
    | zero => cases h; exact ⟨one, rfl, sortOf_one⟩
    | succ i => simp at h
  · rw [clauses_eq] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact cl0_fails_one
    · rw [hpx'] at hlt; exact absurd hlt (Nat.lt_irrefl _)

/-- **`f(0)` has no result**: `f(0) => g(Y)` does not apply (Y has no value), does not fail (its
pattern denotes 0 and it has no condition), and blocks the `[owise]` clause and the rest. -/
theorem f0_none : ¬ ∃ r, Eval c 388 [zero] r := by
  obtain ⟨-, -, h0v, h0r, h0e, -, h0prio, -, -, hex, -, hpx', -, hlv⟩ := fF_shape
  have hmem0 : cl0 ∈ fF.clauses := by rw [clauses_eq]; simp
  have not_fails : ¬ Fails c [zero] cl0 := by
    rintro ⟨h⟩
    cases h [] (fun i hi => by rw [hlv] at hi; cases hi) (by rw [cl0_pats]; exact .cons .dv .nil) with
    | intro ht _ _ => rw [ht] at h0r; cases h0r
    | pre h => rw [cl0_pre] at h; exact absurd (Holds.top_eq h) (by simp)
  have no_apply : ∀ σ, ¬ c.WellSorted cl0.vars σ := fun σ hσ => by
    obtain ⟨v, -, hv⟩ := hσ 0 33 (by rw [h0v]; rfl)
    exact no_E v hv
  rintro ⟨_, hr⟩
  cases hr with
  | clause hfn hmem hσ _ _ _ hprio _ _ =>
    rw [lookupF] at hfn; cases hfn
    rw [clauses_eq] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact no_apply _ hσ
    · exact not_fails (hprio cl0 hmem0 (by decide +kernel) (by rw [h0prio, hpx']; decide))
  | rest hfn hnone =>
    rw [lookupF] at hfn; cases hfn
    exact not_fails (hnone cl0 hmem0)
  | ensFails hfn hmem _ _ _ _ _ _ ht _ _ =>
    rw [lookupF] at hfn; cases hfn
    rw [clauses_eq] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · rw [ht] at h0e; cases h0e
    · rw [ht] at hex; cases hex
  | clauseEx hfn hmem _ _ _ _ _ hne =>
    rw [lookupF] at hfn; cases hfn
    rw [clauses_eq] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> exact absurd (by rfl) hne
  | exNone hfn hmem hne =>
    rw [lookupF] at hfn; cases hfn
    rw [clauses_eq] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> exact absurd (by rfl) hne

/--
info: 'ClauseRhsEmpty.Owise.f0_none' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms f0_none

end Owise

/-- info: ClauseRhsEmpty.Owise.f1_is_a : Eval Owise.c 388 [Owise.one] (some (GroundTerm.ctor 386 [])) -/
#guard_msgs in #check Owise.f1_is_a

end ClauseRhsEmpty
