/-
  The second model with Empty inhabited (KcoreSpec/ModelEmptyInhabited.lean) on K 7.1.337 kompile's
  texts with a function whose clause holds a variable of the sort Empty, which has no production.
  Run from the package root: `lake env lean -j1 test/ModelEmptyInhabited.lean`.

  For each text, `cP := EmptyInh.plus c 33` (Empty is sort 33) is c with one open generator of sort
  Empty, a constant. The hypotheses of `EmptyInh.premises_sub` hold: c has no overloading symbol and
  no parameter, no constructor bears the added number, Empty has no generator, the interpretation
  of the parsed data gives no value anywhere (so the fallbacks agree), every function has at each
  argument list of its sorts a clause that does not fail (so no point of c has every clause failing),
  and `cP` reads a confined sort and holds only Bool's literals in Bool, as c does. `cP` is
  `coreOK` and `FnHyp cP` holds (`fnHypP`): the variable of Empty is held by the added constant,
  the one value of Empty in `cP` (`EmptyInh.value_E_eq`), which makes the named clause match
  independent. So `model` gives an interpretation of both theories, and in it Empty holds an
  element (`inhabited`).

  - `Rhs` (`f2-examples/rhsempty.kompile.kore`): `rule f() => g(Y:Empty) [unboundVariables(Y)]`.
  - `Owise` (`f2-examples/rhsemptyowise.kompile.kore`): `rule f(0) => g(Y:Empty)` beside
    `rule f(_) => a [owise]`.
  - `Genless` (`f2-examples/clgenless.kompile.kore`): `S ::= "a" | c(Empty)`,
    `rule f(_) => 1 requires isC(H:S) [unboundVariables(H)]` beside `rule f(_) => 0 [owise]`.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

open KCore KCore.EmptyInh KCore.Faithful

namespace EmptyInhFixtures

/-! ## e2-clause-rhs-empty -/

namespace Rhs

definition_of defn from "f2-examples/rhsempty.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

noncomputable abbrev cP : Semantics := plus c 33

example : c.symName 387 = "Lblf" ∧ c.sortName 33 = "Empty" ∧ eSym c = 388 := by
  decide +kernel

/-- What the transfer reads of c and `cP`. -/
theorem facts : c.ovls = [] ∧ c.params = [] ∧ c.ctorSigs.all (·.name != eSym c) = true ∧ c.gens 33 = [] ∧
    (c.readsConfined = true → cP.readsConfined = true) ∧ (c.litSort Srt.bool = true → cP.litSort Srt.bool = true) := by
  decide +kernel

theorem hooksNone : ∀ f vs, c.hooks.app f vs = none := fun _ _ => rfl

/-- What `value_E_eq` asks of Empty. -/
theorem empty : c.ctorSigs.all (·.result != 33) = true ∧ c.subsorts.all (fun p => p.2 != 33) = true ∧
    c.collOf 33 = none ∧ c.lib.carriers.all (·.1 != 33) = true ∧
    ((33 : Srt) != Srt.int && (33 : Srt) != Srt.bool && (33 : Srt) != Srt.kconfigVar && (33 : Srt) != Srt.string &&
      (33 : Srt) != Srt.bytes && (33 : Srt) != Srt.float && !c.lib.tokenSorts.contains 33 &&
      !c.lib.byteSorts.contains 33) = true := by
  decide +kernel

theorem fresh : ∀ k ∈ c.ctorSigs, k.name ≠ eSym c := fun k hk => by
  simpa using List.all_eq_true.mp facts.2.2.1 k hk

theorem freshP : ∀ k ∈ c.params, k.sig.name ≠ eSym c := fun k hk => by
  rw [facts.2.1] at hk; cases hk

theorem noRaw : ∀ k ∈ c.params, k.raw = false := fun k hk => by rw [facts.2.1] at hk; cases hk

/-- **The added constant is the one value of Empty in `cP`.** -/
theorem sortOf_e : cP.sortOf (eVal c) = some 33 :=
  EmptyInh.sortOf_e facts.1 fresh freshP (keepsRaw_of_none hooksNone)

theorem value_eq {v : GroundTerm} (h : cP.sortOf v = some 33) : v = eVal c :=
  value_E_eq empty.1 facts.1 noRaw empty.2.1 empty.2.2.1 empty.2.2.2.1 empty.2.2.2.2 h

noncomputable def fF : Fn := c.fns[0]'(by decide +kernel)
noncomputable def clY : Clause := fF.clauses[0]'(by decide +kernel)

theorem fF_mem : fF ∈ c.fns := List.getElem_mem _

/-- `f() => g(Y:Empty)`, alone. -/
theorem shape : c.fns.length = 1 ∧ fF.label = 387 ∧ fF.args = [] ∧ fF.clauses.length = 1 ∧
    clY.vars = [33] ∧ clY.leftVars = [] ∧ clY.exs = [] := by
  decide +kernel

theorem clY_pats : clY.pats = [] := by rfl
theorem clY_req : clY.req = none := by rfl
theorem clY_ens : clY.ens = none := by rfl
theorem clY_rhs : clY.rhs = .app 386 [.var 0] := by rfl
theorem clY_pre : clY.pre = .top := by rfl

theorem fns_eq : c.fns = [fF] := by
  apply List.ext_getElem (by rw [shape.1]; rfl)
  intro i h1 _
  have : i < 1 := shape.1 ▸ h1
  match i, this with
  | 0, _ => rfl

theorem clauses_eq : fF.clauses = [clY] := by
  apply List.ext_getElem (by rw [shape.2.2.2.1]; rfl)
  intro i h1 _
  have : i < 1 := shape.2.2.2.1 ▸ h1
  match i, this with
  | 0, _ => rfl

/-- `f()`'s clause does not fail at `[]`: it has no pattern and no `requires`. -/
theorem noFail : ∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∃ cl ∈ fn.clauses, ¬ Fails c vs cl := by
  intro fn hfn vs hvs
  rw [fns_eq, List.mem_singleton] at hfn
  subst hfn
  rw [shape.2.2.1] at hvs
  rw [sortsOf_nil_of hvs, clauses_eq]
  exact ⟨clY, List.mem_singleton_self _, not_fails_nil clY_pats shape.2.2.2.2.2.1 clY_req clY_pre⟩

/-- **Every premise of c's theory is one of `cP`'s.** -/
theorem sub : ∀ φ, φ ∈ Γc c ∪ Γstep c → φ ∈ Γc cP ∪ Γstep cP :=
  premises_sub facts.1 fresh facts.2.2.2.1
    (fun k hk => by rw [facts.2.1] at hk; cases hk)
    (fun k _ vs _ _ _ => fallback_plus_of_none hooksNone k.name vs)
    (hfails_of_noFail noFail) facts.2.2.2.2.1 facts.2.2.2.2.2

/-- The lists the package states of `cP`: `coreOK`, `f` named for the held variables and its clause
for match independence, nothing else. -/
theorem namedP : cP.coreOK = true ∧ cP.heldObligations = [387] ∧
    cP.rankObligations [387] ++ cP.decObligationsL = [] ∧ cP.totalObligationsRP [387] [] = [] ∧
    cP.agreeObligationsI = [] ∧ cP.matchObligationsL = [(387, 0)] ∧ cP.owedRules = [] ∧
    cP.owedClauses = [] := by
  decide_cheap

theorem coreP : cP.coreOK = true := namedP.1

theorem lookupF : cP.lookupFn 387 = some fF :=
  shape.2.1 ▸ lookupFn_of_core coreP (show fF ∈ cP.fns from fF_mem)

theorem lookupF_eq {fn : Fn} (h : cP.lookupFn 387 = some fn) : fn = fF :=
  Option.some.inj (h.symm.trans lookupF)

/-- **`f`'s variable is held in `cP`**: Empty has the added constant. -/
theorem held : ∀ f ∈ cP.heldObligations, HeldOwed cP f := by
  intro f hf fn hfn
  rw [namedP.2.1, List.mem_singleton] at hf
  subst hf
  have e := lookupF_eq hfn
  subst e
  refine .inl fun cl hcl i s hi => .inr ?_
  rw [clauses_eq, List.mem_singleton] at hcl
  subst hcl
  rw [shape.2.2.2.2.1] at hi
  cases i with
  | zero => cases hi; exact ⟨eVal c, sortOf_e⟩
  | succ i => simp at hi

/-- **`f() => g(Y)` is match independent in `cP`**: Y has one value. -/
theorem matchY : MatchIndependent cP clY := by
  obtain ⟨-, -, -, -, hv, -, hx⟩ := shape
  have he := clY_ens
  have hrhs := clY_rhs
  refine (matchIndependent_iff_noExs hx).mpr fun vs σ σ' ha ha' _ _ _ _ _ => .inl
    ⟨hx, hx, rfl, rfl, fun i hi => ?_, fun t ht => by rw [he] at ht; cases ht⟩
  rw [hrhs] at hi
  simp [varOccs, varOccsList] at hi
  subst hi
  have h0 : (0 : Nat) ∈ clY.univ := by simp [Clause.univ, hv, hx]
  obtain ⟨v, hv1, hv2⟩ := ha.1 0 h0 33 (by rw [hv]; rfl)
  obtain ⟨w, hw1, hw2⟩ := ha'.1 0 h0 33 (by rw [hv]; rfl)
  rw [hv1, hw1, value_eq hv2, value_eq hw2]

theorem oblP : FnObligations cP [387] [] := by
  obtain ⟨-, -, hterm, htot, hagr, hmat, howR, howC⟩ := namedP
  refine ⟨fun f hf => (by rw [hterm] at hf; cases hf), fun f hf => (by rw [htot] at hf; cases hf),
    fun f hf => (by rw [hagr] at hf; cases hf), fun p hp fn hfn cl hcl => ?_,
    ⟨openRules_of_owed (by rw [howR]; intro i hi; cases hi),
     openClauses_of_owed (by rw [howC]; intro p hp; cases hp)⟩, ?_⟩
  · rw [hmat, List.mem_singleton] at hp
    subst hp
    have e := lookupF_eq hfn
    subst e
    rw [clauses_eq] at hcl
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hcl
    subst hcl
    exact matchY
  · intro k hk _
    have hk' : k ∈ c.params ++ [eParam c 33] := hk
    rw [facts.2.1, List.nil_append, List.mem_singleton] at hk'
    subst hk'
    exact ⟨fun h => by simp [eParam] at h, fun h => by simp [eParam] at h⟩

theorem fnHypP : FnHyp cP := fnHyp_of_fnObligationsN coreP held ParamsTotal.nil oblP

/-- **An interpretation of both theories.** -/
theorem model : ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc cP ∪ Γstep cP)) ∧ (I ⊧ᴵP (Γc c ∪ Γstep c)) :=
  model_exists sub coreP fnHypP

/-- **In it Empty holds an element**, the added constant's. -/
theorem inhabited : ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      (I ⊧ᴵ KoreAML.sExists ⟨1⟩ (sortP (c.sortName 33)) (den c (eVal c) ≡ .evar ⟨1⟩)) := by
  obtain ⟨M, hM, I, hP, hc⟩ := model
  exact ⟨M, hM, I, hc, inhabited_of_plus facts.1 fresh freshP (keepsRaw_of_none hooksNone) hP⟩

/--
info: 'EmptyInhFixtures.Rhs.inhabited' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms inhabited

end Rhs

/-! ## e2-clause-rhs-empty-owise -/

namespace Owise

definition_of defn from "f2-examples/rhsemptyowise.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

noncomputable abbrev cP : Semantics := plus c 33

/-- What the transfer reads of c and `cP`. -/
theorem facts : c.ovls = [] ∧ c.params = [] ∧ c.ctorSigs.all (·.name != eSym c) = true ∧ c.gens 33 = [] ∧
    (c.readsConfined = true → cP.readsConfined = true) ∧ (c.litSort Srt.bool = true → cP.litSort Srt.bool = true) := by
  decide +kernel

theorem hooksNone : ∀ f vs, c.hooks.app f vs = none := fun _ _ => rfl

theorem fresh : ∀ k ∈ c.ctorSigs, k.name ≠ eSym c := fun k hk => by
  simpa using List.all_eq_true.mp facts.2.2.1 k hk

theorem freshP : ∀ k ∈ c.params, k.sig.name ≠ eSym c := fun k hk => by
  rw [facts.2.1] at hk; cases hk

theorem sortOf_e : cP.sortOf (eVal c) = some 33 :=
  EmptyInh.sortOf_e facts.1 fresh freshP (keepsRaw_of_none hooksNone)

theorem openLawsP : OpenLaws cP := by
  intro k hk _
  have hk' : k ∈ c.params ++ [eParam c 33] := hk
  rw [facts.2.1, List.nil_append, List.mem_singleton] at hk'
  subst hk'
  exact ⟨fun h => by simp [eParam] at h, fun h => by simp [eParam] at h⟩

example : c.symName 388 = "Lblf" ∧ c.sortName 33 = "Empty" ∧ eSym c = 389 := by
  decide +kernel

theorem empty : c.ctorSigs.all (·.result != 33) = true ∧ c.subsorts.all (fun p => p.2 != 33) = true ∧
    c.collOf 33 = none ∧ c.lib.carriers.all (·.1 != 33) = true ∧
    ((33 : Srt) != Srt.int && (33 : Srt) != Srt.bool && (33 : Srt) != Srt.kconfigVar && (33 : Srt) != Srt.string &&
      (33 : Srt) != Srt.bytes && (33 : Srt) != Srt.float && !c.lib.tokenSorts.contains 33 &&
      !c.lib.byteSorts.contains 33) = true := by
  decide +kernel

theorem noRaw : ∀ k ∈ c.params, k.raw = false := fun k hk => by rw [facts.2.1] at hk; cases hk

theorem value_eq {v : GroundTerm} (h : cP.sortOf v = some 33) : v = eVal c :=
  value_E_eq empty.1 facts.1 noRaw empty.2.1 empty.2.2.1 empty.2.2.2.1 empty.2.2.2.2 h

noncomputable def fF : Fn := c.fns[0]'(by decide +kernel)
noncomputable def cl0 : Clause := fF.clauses[0]'(by decide +kernel)
noncomputable def clX : Clause := fF.clauses[1]'(by decide +kernel)

theorem fF_mem : fF ∈ c.fns := List.getElem_mem _

/-- `f(0) => g(Y:Empty)` and `f(X:Int) => a` (the `[owise]` one). -/
theorem shape : c.fns.length = 1 ∧ fF.label = 388 ∧ fF.args = [Srt.int] ∧ fF.clauses.length = 2 ∧
    cl0.vars = [33] ∧ cl0.leftVars = [] ∧ cl0.exs = [] ∧ clX.vars = [Srt.int] ∧ clX.leftVars = [0] := by
  decide +kernel

theorem cl0_ens : cl0.ens = none := by rfl
theorem cl0_rhs : cl0.rhs = .app 387 [.var 0] := by rfl
theorem clX_pats : clX.pats = [.var 0] := by rfl
theorem clX_req : clX.req = none := by rfl
theorem clX_pre : clX.pre = .top := by rfl

theorem fns_eq : c.fns = [fF] := by
  apply List.ext_getElem (by rw [shape.1]; rfl)
  intro i h1 _
  have : i < 1 := shape.1 ▸ h1
  match i, this with
  | 0, _ => rfl

theorem clauses_eq : fF.clauses = [cl0, clX] := by
  apply List.ext_getElem (by rw [shape.2.2.2.1]; rfl)
  intro i h1 _
  have : i < 2 := shape.2.2.2.1 ▸ h1
  match i, this with
  | 0, _ => rfl
  | 1, _ => rfl

/-- The `[owise]` clause does not fail at an Int. -/
theorem noFail : ∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∃ cl ∈ fn.clauses, ¬ Fails c vs cl := by
  intro fn hfn vs hvs
  rw [fns_eq, List.mem_singleton] at hfn
  subst hfn
  rw [shape.2.2.1] at hvs
  obtain ⟨v, rfl, hv⟩ := sortsOf_single hvs
  exact ⟨clX, by rw [clauses_eq]; simp, not_fails_var shape.2.2.2.2.2.2.2.1 clX_pats clX_req clX_pre hv⟩

theorem sub : ∀ φ, φ ∈ Γc c ∪ Γstep c → φ ∈ Γc cP ∪ Γstep cP :=
  premises_sub facts.1 fresh facts.2.2.2.1
    (fun k hk => by rw [facts.2.1] at hk; cases hk)
    (fun k _ vs _ _ _ => fallback_plus_of_none hooksNone k.name vs)
    (hfails_of_noFail noFail) facts.2.2.2.2.1 facts.2.2.2.2.2

theorem namedP : cP.coreOK = true ∧ cP.heldObligations = [388] ∧
    cP.rankObligations [388] ++ cP.decObligationsL = [] ∧ cP.totalObligationsRP [388] [] = [] ∧
    cP.agreeObligationsI = [] ∧ cP.matchObligationsL = [(388, 0)] ∧ cP.owedRules = [] ∧
    cP.owedClauses = [] := by
  decide_cheap

theorem coreP : cP.coreOK = true := namedP.1

theorem lookupF : cP.lookupFn 388 = some fF :=
  shape.2.1 ▸ lookupFn_of_core coreP (show fF ∈ cP.fns from fF_mem)

theorem lookupF_eq {fn : Fn} (h : cP.lookupFn 388 = some fn) : fn = fF :=
  Option.some.inj (h.symm.trans lookupF)

/-- `f(0) => g(Y)`'s variable is held by the added constant, `f(X) => a`'s by its pattern. -/
theorem held : ∀ f ∈ cP.heldObligations, HeldOwed cP f := by
  intro f hf fn hfn
  rw [namedP.2.1, List.mem_singleton] at hf
  subst hf
  have e := lookupF_eq hfn
  subst e
  refine .inl fun cl hcl i s hi => ?_
  rw [clauses_eq] at hcl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcl
  rcases hcl with rfl | rfl
  · rw [shape.2.2.2.2.1] at hi
    cases i with
    | zero => cases hi; exact .inr ⟨eVal c, sortOf_e⟩
    | succ i => simp at hi
  · rw [shape.2.2.2.2.2.2.2.1] at hi
    cases i with
    | zero => exact .inl (by rw [shape.2.2.2.2.2.2.2.2]; simp)
    | succ i => simp at hi

theorem match0 : MatchIndependent cP cl0 := by
  obtain ⟨-, -, -, -, hv, -, hx, -⟩ := shape
  have he := cl0_ens
  have hrhs := cl0_rhs
  refine (matchIndependent_iff_noExs hx).mpr fun vs σ σ' ha ha' _ _ _ _ _ => .inl
    ⟨hx, hx, rfl, rfl, fun i hi => ?_, fun t ht => by rw [he] at ht; cases ht⟩
  rw [hrhs] at hi
  simp [varOccs, varOccsList] at hi
  subst hi
  have h0 : (0 : Nat) ∈ cl0.univ := by simp [Clause.univ, hv, hx]
  obtain ⟨v, hv1, hv2⟩ := ha.1 0 h0 33 (by rw [hv]; rfl)
  obtain ⟨w, hw1, hw2⟩ := ha'.1 0 h0 33 (by rw [hv]; rfl)
  rw [hv1, hw1, value_eq hv2, value_eq hw2]

theorem oblP : FnObligations cP [388] [] := by
  obtain ⟨-, -, hterm, htot, hagr, hmat, howR, howC⟩ := namedP
  refine ⟨fun f hf => (by rw [hterm] at hf; cases hf), fun f hf => (by rw [htot] at hf; cases hf),
    fun f hf => (by rw [hagr] at hf; cases hf), fun p hp fn hfn cl hcl => ?_,
    ⟨openRules_of_owed (by rw [howR]; intro i hi; cases hi),
     openClauses_of_owed (by rw [howC]; intro p hp; cases hp)⟩, openLawsP⟩
  rw [hmat, List.mem_singleton] at hp
  subst hp
  have e := lookupF_eq hfn
  subst e
  rw [clauses_eq] at hcl
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hcl
  subst hcl
  exact match0

theorem fnHypP : FnHyp cP := fnHyp_of_fnObligationsN coreP held ParamsTotal.nil oblP

theorem model : ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc cP ∪ Γstep cP)) ∧ (I ⊧ᴵP (Γc c ∪ Γstep c)) :=
  model_exists sub coreP fnHypP

theorem inhabited : ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      (I ⊧ᴵ KoreAML.sExists ⟨1⟩ (sortP (c.sortName 33)) (den c (eVal c) ≡ .evar ⟨1⟩)) := by
  obtain ⟨M, hM, I, hP, hc⟩ := model
  exact ⟨M, hM, I, hc, inhabited_of_plus facts.1 fresh freshP (keepsRaw_of_none hooksNone) hP⟩

/--
info: 'EmptyInhFixtures.Owise.inhabited' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms inhabited

end Owise

/-! ## e2-clause-genless-arg -/

namespace Genless

definition_of defn from "f2-examples/clgenless.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem

noncomputable abbrev cP : Semantics := plus c 33

/-- What the transfer reads of c and `cP`. -/
theorem facts : c.ovls = [] ∧ c.params = [] ∧ c.ctorSigs.all (·.name != eSym c) = true ∧ c.gens 33 = [] ∧
    (c.readsConfined = true → cP.readsConfined = true) ∧ (c.litSort Srt.bool = true → cP.litSort Srt.bool = true) := by
  decide +kernel

theorem hooksNone : ∀ f vs, c.hooks.app f vs = none := fun _ _ => rfl

theorem fresh : ∀ k ∈ c.ctorSigs, k.name ≠ eSym c := fun k hk => by
  simpa using List.all_eq_true.mp facts.2.2.1 k hk

theorem freshP : ∀ k ∈ c.params, k.sig.name ≠ eSym c := fun k hk => by
  rw [facts.2.1] at hk; cases hk

theorem sortOf_e : cP.sortOf (eVal c) = some 33 :=
  EmptyInh.sortOf_e facts.1 fresh freshP (keepsRaw_of_none hooksNone)

theorem openLawsP : OpenLaws cP := by
  intro k hk _
  have hk' : k ∈ c.params ++ [eParam c 33] := hk
  rw [facts.2.1, List.nil_append, List.mem_singleton] at hk'
  subst hk'
  exact ⟨fun h => by simp [eParam] at h, fun h => by simp [eParam] at h⟩

example : c.symName 389 = "Lblf" ∧ c.symName 390 = "LblisC" ∧ c.sortName 33 = "Empty" ∧
    c.sortName 32 = "S" ∧ eSym c = 391 := by
  decide +kernel

noncomputable def fF : Fn := c.fns[0]'(by decide +kernel)
noncomputable def fC : Fn := c.fns[1]'(by decide +kernel)
noncomputable def cl0 : Clause := fF.clauses[0]'(by decide +kernel)
noncomputable def clX : Clause := fF.clauses[1]'(by decide +kernel)
noncomputable def clC : Clause := fC.clauses[1]'(by decide +kernel)

theorem fF_mem : fF ∈ c.fns := List.getElem_mem _

/-- `f(_) => 1 requires isC(H)` and `f(X:Int) => 0` (the `[owise]` one); `isC(X:S) => false` (the
`[owise]` one of `isC`). -/
theorem shape : c.fns.length = 2 ∧ fF.label = 389 ∧ fF.args = [Srt.int] ∧ fF.clauses.length = 2 ∧
    fC.args = [32] ∧ fC.clauses.length = 2 ∧ cl0.exs = [] ∧ clX.vars = [Srt.int] ∧ clC.vars = [32] := by
  decide +kernel

theorem cl0_ens : cl0.ens = none := by rfl
theorem cl0_rhs : cl0.rhs = .dv Srt.int (.int 1) := by rfl
theorem clX_pats : clX.pats = [.var 0] := by rfl
theorem clX_req : clX.req = none := by rfl
theorem clX_pre : clX.pre = .top := by rfl
theorem clC_pats : clC.pats = [.var 0] := by rfl
theorem clC_req : clC.req = none := by rfl
theorem clC_pre : clC.pre = .top := by rfl

theorem fns_eq : c.fns = [fF, fC] := by
  apply List.ext_getElem (by rw [shape.1]; rfl)
  intro i h1 _
  have : i < 2 := shape.1 ▸ h1
  match i, this with
  | 0, _ => rfl
  | 1, _ => rfl

theorem clauses_eq : fF.clauses = [cl0, clX] := by
  apply List.ext_getElem (by rw [shape.2.2.2.1]; rfl)
  intro i h1 _
  have : i < 2 := shape.2.2.2.1 ▸ h1
  match i, this with
  | 0, _ => rfl
  | 1, _ => rfl

theorem clC_mem : clC ∈ fC.clauses := List.getElem_mem _

/-- The `[owise]` clauses of `f` and `isC` do not fail at a value of their argument sort. -/
theorem noFail : ∀ fn ∈ c.fns, ∀ vs, c.sortsOf vs = some fn.args → ∃ cl ∈ fn.clauses, ¬ Fails c vs cl := by
  intro fn hfn vs hvs
  obtain ⟨-, -, hfa, -, hca, -, -, hxv, hcv⟩ := shape
  rw [fns_eq] at hfn
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfn
  rcases hfn with rfl | rfl
  · rw [hfa] at hvs
    obtain ⟨v, rfl, hv⟩ := sortsOf_single hvs
    exact ⟨clX, by rw [clauses_eq]; simp, not_fails_var hxv clX_pats clX_req clX_pre hv⟩
  · rw [hca] at hvs
    obtain ⟨v, rfl, hv⟩ := sortsOf_single hvs
    exact ⟨clC, clC_mem, not_fails_var hcv clC_pats clC_req clC_pre hv⟩

theorem sub : ∀ φ, φ ∈ Γc c ∪ Γstep c → φ ∈ Γc cP ∪ Γstep cP :=
  premises_sub facts.1 fresh facts.2.2.2.1
    (fun k hk => by rw [facts.2.1] at hk; cases hk)
    (fun k _ vs _ _ _ => fallback_plus_of_none hooksNone k.name vs)
    (hfails_of_noFail noFail) facts.2.2.2.2.1 facts.2.2.2.2.2

/-- The rank `isC` before `f` shows both terminate; only `f`'s first clause is named, for match
independence. -/
theorem namedP : cP.coreOK = true ∧ cP.heldObligations = [] ∧
    cP.rankObligations [390, 389] ++ cP.decObligationsL = [] ∧ cP.totalObligationsRP [390, 389] [] = [] ∧
    cP.agreeObligationsI = [] ∧ cP.matchObligationsL = [(389, 0)] ∧ cP.owedRules = [] ∧
    cP.owedClauses = [] := by
  decide_cheap

theorem coreP : cP.coreOK = true := namedP.1

theorem lookupF : cP.lookupFn 389 = some fF :=
  shape.2.1 ▸ lookupFn_of_core coreP (show fF ∈ cP.fns from fF_mem)

theorem lookupF_eq {fn : Fn} (h : cP.lookupFn 389 = some fn) : fn = fF :=
  Option.some.inj (h.symm.trans lookupF)

/-- `f(_) => 1 requires isC(H)` is match independent: its right side is a literal. -/
theorem match0 : MatchIndependent cP cl0 := by
  have hx := shape.2.2.2.2.2.2.1
  have he := cl0_ens
  have hrhs := cl0_rhs
  refine (matchIndependent_iff_noExs hx).mpr fun vs σ σ' _ _ _ _ _ _ _ => .inl
    ⟨hx, hx, rfl, rfl, fun i hi => ?_, fun t ht => by rw [he] at ht; cases ht⟩
  rw [hrhs] at hi
  simp [varOccs] at hi

theorem oblP : FnObligations cP [390, 389] [] := by
  obtain ⟨-, -, hterm, htot, hagr, hmat, howR, howC⟩ := namedP
  refine ⟨fun f hf => (by rw [hterm] at hf; cases hf), fun f hf => (by rw [htot] at hf; cases hf),
    fun f hf => (by rw [hagr] at hf; cases hf), fun p hp fn hfn cl hcl => ?_,
    ⟨openRules_of_owed (by rw [howR]; intro i hi; cases hi),
     openClauses_of_owed (by rw [howC]; intro p hp; cases hp)⟩, openLawsP⟩
  rw [hmat, List.mem_singleton] at hp
  subst hp
  have e := lookupF_eq hfn
  subst e
  rw [clauses_eq] at hcl
  simp only [List.getElem?_cons_zero, Option.some.injEq] at hcl
  subst hcl
  exact match0

theorem fnHypP : FnHyp cP :=
  fnHyp_of_fnObligationsN coreP (by rw [namedP.2.1]; intro f hf; cases hf) ParamsTotal.nil oblP

theorem model : ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc cP ∪ Γstep cP)) ∧ (I ⊧ᴵP (Γc c ∪ Γstep c)) :=
  model_exists sub coreP fnHypP

theorem inhabited : ∃ (M : Type) (_ : Inhabited M) (I : ML.Interpretation KoreAML.Sym M),
    (I ⊧ᴵP (Γc c ∪ Γstep c)) ∧
      (I ⊧ᴵ KoreAML.sExists ⟨1⟩ (sortP (c.sortName 33)) (den c (eVal c) ≡ .evar ⟨1⟩)) := by
  obtain ⟨M, hM, I, hP, hc⟩ := model
  exact ⟨M, hM, I, hc, inhabited_of_plus facts.1 fresh freshP (keepsRaw_of_none hooksNone) hP⟩

/--
info: 'EmptyInhFixtures.Genless.inhabited' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms inhabited

end Genless

end EmptyInhFixtures
