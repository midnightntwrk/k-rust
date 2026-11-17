/-
  Clauses with a variable that only the right side holds, on a hand-built semantics. Run from the
  package root: `lake env lean test/RightOnly.lean`. Kernel-checked (`decide +kernel`).

  The semantics `c`: the sorts U (`U ::= u`), T and Empty (no constructor, no value); the
  constructors `u : U`, `g : Empty → T`, `h : U → T`, `k : Int → T`, `a : T`; the functions
  - `fE() = g(Y:Empty)` (`clE`),
  - `fEA() = g(Y:Empty)` and `fEA() = a` at one priority (`clE`, `clA`),
  - `fU() = h(Y:U)` (`clU`),
  - `fI() = k(Y:Int)` (`clI`).
  `cV` holds `fU`, `fI` and `q(B:Bool) = h(Y:U) requires B` (`fQ`, `clQ`) only, `cX` the function
  `p(X:Int) = X` (`clX`), whose pattern binds its variable.

  `Semantics.valued` and `valued_value` at U, T, Int and Bool, not at Empty; `rightHeld_of_valued`
  at `cV` (each right-only variable of a sort `valued` accepts) and `rightValued` false at `c`
  (Empty); `rightHeld_of_binds` at `cX`; `RightHeld` and `rightValued` under `withHooks`;
  `extendHeld` at `clI` and `Clause.appliesAt_extendRH` at `clU`, in `cV`; `clQ` fails at `[false]`
  (`Clause.fails_of_not_appliesRH`, `clQ_fails`) and `q(false)` has a result (`eval_resultRH`).

  At the level of `Eval`, the facts of each fixture (no value has sort Empty: `no_E`; `u` is U's
  only value: `u_only`):
  - `fE`: C1 (`no_result`: a matched clause, not `aside`, of the smallest priority, without a
    `requires`, with a variable of a sort without a value) instantiated: `Eval c fE []` has no
    result (`fE_none`).
  - `fEA` alone (`cEA`): `clA` decides, `clE` not stopping it (`peer_decides`): `fEA()` is `a`
    (`fEA_a`). `clE` applies under no substitution, so it is coherent with every clause on either
    side and match independent (`coherent_left`, `coherent_right`); `FnHyp cEA` holds, by hand
    (`fnHyp_cEA`), while `rightValued` fails and `RightHeld` is false there (`not_rightHeld_cEA`).
  - `fU`: `fU()` is `h(u)` (`fU_hu`), and `clU` is match independent (`matchIndependent_U`).
  - `fI`: Y = 0 and Y = 1 both decide `fI()`, with `k(0)` and `k(1)`: `clI` is not match
    independent (`not_matchIndependent_I`).
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.RightOnlyTest

open KCore

def U : Srt := nRegSorts
def T : Srt := nRegSorts + 1
def E : Srt := nRegSorts + 2

def uL : Sym := nRegSyms
def gL : Sym := nRegSyms + 1
def hL : Sym := nRegSyms + 2
def kL : Sym := nRegSyms + 3
def aL : Sym := nRegSyms + 4
def fEL : Sym := nRegSyms + 5
def fEAL : Sym := nRegSyms + 6
def fUL : Sym := nRegSyms + 7
def fIL : Sym := nRegSyms + 8
def pL : Sym := nRegSyms + 9
def qL : Sym := nRegSyms + 10

/-- `f() = g(Y:Empty)` -/
def clE : Clause := { vars := [E], pats := [], req := none, rhs := .app gL [.var 0], ens := none }
/-- `f() = a` -/
def clA : Clause := { vars := [], pats := [], req := none, rhs := .app aL [], ens := none }
/-- `f() = h(Y:U)` -/
def clU : Clause := { vars := [U], pats := [], req := none, rhs := .app hL [.var 0], ens := none }
/-- `f() = k(Y:Int)` -/
def clI : Clause := { vars := [Srt.int], pats := [], req := none, rhs := .app kL [.var 0], ens := none }
/-- `p(X:Int) = X` -/
def clX : Clause := { vars := [Srt.int], pats := [.var 0], req := none, rhs := .var 0, ens := none }
/-- `q(B:Bool) = h(Y:U) requires B` -/
def clQ : Clause := { vars := [Srt.bool, U], pats := [.var 0], req := some (.var 0), rhs := .app hL [.var 1], ens := none }

def fE : Fn := { label := fEL, args := [], result := T, clauses := [clE] }
def fEA : Fn := { label := fEAL, args := [], result := T, clauses := [clE, clA] }
def fU : Fn := { label := fUL, args := [], result := T, clauses := [clU] }
def fI : Fn := { label := fIL, args := [], result := T, clauses := [clI] }
def fX : Fn := { label := pL, args := [Srt.int], result := Srt.int, clauses := [clX] }
def fQ : Fn := { label := qL, args := [Srt.bool], result := T, clauses := [clQ] }

def c : Semantics :=
  { lib := { sortsBelowKItem := [Srt.int, Srt.bool] }
    sortNames := ["U", "T", "Empty"]
    symNames := ["Lblu", "Lblg", "Lblh", "Lblk", "Lbla", "LblfE", "LblfEA", "LblfU", "LblfI", "Lblp", "Lblq"]
    userSorts := [U, T, E]
    ctors := [⟨uL, [], U⟩, ⟨gL, [E], T⟩, ⟨hL, [U], T⟩, ⟨kL, [Srt.int], T⟩, ⟨aL, [], T⟩]
    fns := [fE, fEA, fU, fI]
    userSubsorts := []
    pgmSort := Srt.k
    rules := [] }

/-- `fU`, `fI` and `q(B:Bool) = h(Y:U) requires B` (`fQ`, `clQ`: a pattern variable read by the
`requires`, and a right-only variable). -/
def cV : Semantics := { c with fns := [fU, fI, fQ] }
def cX : Semantics := { c with fns := [fX] }

/-! ## `valued` -/

/-- U (`u`), T (`a`), Int and Bool are `valued`; Empty is not. -/
theorem valued_sorts : c.valued U = true ∧ c.valued T = true ∧ c.valued Srt.int = true ∧
    c.valued Srt.bool = true ∧ c.valued E = false := by decide +kernel

/-- `valued_value` at each: a value of U, of T, of Int, of Bool. -/
example : (∃ v, c.sortOf v = some U) ∧ (∃ v, c.sortOf v = some T) ∧ (∃ v, c.sortOf v = some Srt.int) ∧
    (∃ v, c.sortOf v = some Srt.bool) :=
  ⟨Semantics.valued_value valued_sorts.1, Semantics.valued_value valued_sorts.2.1,
   Semantics.valued_value valued_sorts.2.2.1, Semantics.valued_value valued_sorts.2.2.2.1⟩

/-- The value `valued_value` exhibits at U is `u`. -/
example : c.sortOf (.ctor uL []) = some U := by decide +kernel

/-! ## `RightHeld` -/

/-- `clU` and `clI` have a variable that their patterns and conditions do not hold, so neither
`clauseSorted` nor `rightHeld_of_binds` reads them; `clE` too. -/
theorem right_only : clU.leftVars = [] ∧ clI.leftVars = [] ∧ clE.leftVars = [] ∧
    binds clU.vars.length (varOccsList clU.pats) = false ∧ binds clI.vars.length (varOccsList clI.pats) = false := by
  decide +kernel

/-- **`rightHeld_of_valued` at `cV`**: the right-only variables are of U and Int. -/
theorem rightHeld_cV : cV.RightHeld := Semantics.rightHeld_of_valued (by decide +kernel)

/-- `rightValued` fails at `c`: `clE`'s variable is of Empty. -/
theorem rightValued_c : c.rightValued = false := by decide +kernel

/-- **`rightHeld_of_binds` at `cX`**: `clX`'s pattern binds its variable. -/
theorem rightHeld_cX : cX.RightHeld := Semantics.rightHeld_of_binds (by decide +kernel)

/-- `RightHeld` and `rightValued` at `cV` under every interpretation of the parameters. -/
example (H : HookParams) : (cV.withHooks H).RightHeld ∧ (cV.withHooks H).rightValued = true :=
  ⟨Semantics.rightHeld_withHooks rightHeld_cV H (by decide +kernel), (Semantics.rightValued_withHooks cV H).trans (by decide +kernel)⟩

/-! ## The extension step -/

/-- **`extendHeld` at `clI`**: the substitution with no entry, well sorted on `clI`'s patterns and
conditions (none), extends to one well sorted on Y:Int. -/
example : ∃ σ', cV.WellSorted clI.vars σ' :=
  (Semantics.extendHeld (rightHeld_cV.heldAt (List.Mem.tail _ (List.Mem.head _)) (List.Mem.head _))
    (σ := []) (fun i hi => by rw [right_only.2.1] at hi; cases hi)).imp fun _ h => h.1

/-- **`appliesAt_extendRH` at `clQ`**: under B ↦ `true`, well sorted on `clQ`'s patterns and
conditions (B), the pattern matches `[true]` and the `requires` is `true`; so `clQ` applies at
`[true]` under an extension of it, which gives Y a value of U and keeps B. -/
example : ∃ σ', clQ.AppliesAt cV σ' [.dv Srt.bool (.bool true)] ∧
    σ'.lookup 0 = some (.dv Srt.bool (.bool true)) := by
  have hσ : cV.WellSortedAt clQ.vars clQ.leftVars [(0, .dv Srt.bool (.bool true))] := fun i hi s hs => by
    have h0 : i = 0 := by simpa [clQ, Clause.leftVars, Clause.condVars, varOccs, varOccsList, varOccsCond] using hi
    subst h0
    simp only [clQ, List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨_, rfl, by decide +kernel⟩
  obtain ⟨σ', ha, hag⟩ := Clause.appliesAt_extendRH
    (rightHeld_cV.heldAt (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.head _)) hσ
    (.cons (.var rfl) .nil) (fun t ht => by cases ht; exact .var) .top
  exact ⟨σ', ha, hag 0 (by simp [clQ, Clause.leftVars, varOccsList, varOccs])⟩

/-- `clQ` applies at `[false]` under no substitution: its pattern gives B `false`, its `requires`
reads B. -/
theorem clQ_not_applies : ¬ ∃ σ, clQ.AppliesAt cV σ [.dv Srt.bool (.bool false)] := fun ⟨σ, _, hm, hq, _⟩ => by
  have h1 := hq (.var 0) rfl
  cases hm with
  | cons hp _ =>
    cases hp with
    | var hl =>
      have := EvalTerm.var_inv h1
      rw [hl] at this; cases this

/-- **`fails_of_not_appliesRH` at `clQ`**: `clQ` (Y:U outside its patterns and conditions) fails at
`[false]`. -/
theorem clQ_fails : Fails cV [.dv Srt.bool (.bool false)] clQ :=
  Clause.fails_of_not_appliesRH (rightHeld_cV.heldAt (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    (List.Mem.head _)) (fun _ _ _ => ⟨(fun t ht => by cases ht; exact ⟨_, .var⟩), true, .top⟩) clQ_not_applies

/-- **`eval_resultRH` at `q`**: `q(false)` has a result in `cV`, `clQ` failing. -/
example : ∃ r, Eval cV qL [.dv Srt.bool (.bool false)] r :=
  eval_resultRH (fn := fQ) rfl
    (fun cl hcl => by
      rw [show fQ.clauses = [clQ] from rfl, List.mem_singleton] at hcl; subst hcl
      exact ⟨rfl, rfl⟩)
    (fun cl hcl => by
      rw [show fQ.clauses = [clQ] from rfl, List.mem_singleton] at hcl; subst hcl
      exact rightHeld_cV.heldAt (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) (List.Mem.head _))
    (fun cl hcl _ _ _ => by
      rw [show fQ.clauses = [clQ] from rfl, List.mem_singleton] at hcl; subst hcl
      exact ⟨(fun t ht => by cases ht; exact ⟨_, .var⟩), true, .top⟩)
    (fun cl hcl σ ha => by
      rw [show fQ.clauses = [clQ] from rfl, List.mem_singleton] at hcl; subst hcl
      exact absurd ⟨σ, ha⟩ clQ_not_applies)
    (fun cl hcl σ ha => by
      rw [show fQ.clauses = [clQ] from rfl, List.mem_singleton] at hcl; subst hcl
      exact absurd ⟨σ, ha⟩ clQ_not_applies)

/-- **`appliesAt_extendRH` at `clU`**: `clU` matches `[]` with no `requires` under the substitution
with no entry, so it applies at `[]` under an extension of it. -/
example : ∃ σ', clU.AppliesAt cV σ' [] :=
  (Clause.appliesAt_extendRH (rightHeld_cV.heldAt (List.Mem.head _) (List.Mem.head _)) (σ := [])
    (fun i hi => by rw [right_only.1] at hi; cases hi) .nil (fun t h => by cases h) .top).imp fun _ h => h.1

/-! ## The values of U and Empty -/

theorem subs_own : c.subsorts.all (fun p => p.2 != U && p.2 != E) = true := by decide +kernel
theorem coll_own : c.collOf U = none ∧ c.collOf E = none := by decide +kernel
theorem ctors_E : c.ctorSigs.all (fun k => k.result != E) = true := by decide +kernel
theorem ctors_U : c.ctorSigs.all (fun k => k.result != U || (k.name == uL && k.args.isEmpty)) = true := by
  decide +kernel

/-- A value of U or of Empty is a constructor term: no literal, injection or collection has either
sort. -/
theorem sortOf_own {s : Srt} (hs : s = U ∨ s = E) {v : GroundTerm} (h : c.sortOf v = some s) :
    ∃ k ∈ c.ctorSigs, k.result = s ∧ ∃ ts, v = .ctor k.name ts ∧ c.sortsOf ts = some k.args := by
  cases v with
  | ctor f ts =>
    rw [Semantics.sortOf] at h
    cases hk : lookupSig c.ctorSigs f with
    | none =>
      have : c.lookupOvl f = none := rfl
      rw [hk, this, c.lookupOpen_of_noRaw (by decide +kernel) f] at h; cases h
    | some k =>
      rw [hk] at h
      simp only at h
      split at h
      · rename_i hts
        have hf := List.find?_some (by rw [← lookupSig_eq]; exact hk)
        have hm := List.mem_of_find?_eq_some (by rw [← lookupSig_eq]; exact hk)
        simp only [beq_iff_eq] at hf hts
        subst hf
        exact ⟨k, hm, Option.some.inj h, ts, rfl, hts⟩
      · cases h
  | inj a b t =>
    rw [Semantics.sortOf] at h
    split at h
    · rename_i h'
      cases h
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h'
      have := List.all_eq_true.mp subs_own _ h'.1.1
      rcases hs with rfl | rfl <;> simp at this
    · cases h
  | dv s' lit =>
    rw [Semantics.sortOf] at h
    split at h
    · rename_i h'
      cases h
      rcases hs with rfl | rfl <;>
      cases lit with
      | int _ => simp only [dvOK, beq_iff_eq] at h'; exact absurd h' (by decide)
      | bool _ => simp only [dvOK, beq_iff_eq] at h'; exact absurd h' (by decide)
      | float _ _ _ => simp only [dvOK, Bool.and_eq_true, beq_iff_eq] at h'; exact absurd h'.1 (by decide)
      | tok t =>
        simp only [dvOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h'
        rcases h' with ((h' | h') | h') | ⟨h' | h', -⟩
        · exact absurd h' (by decide)
        · exact absurd h' (by decide)
        · exact absurd h' (by decide +kernel)
        · exact absurd h' (by decide)
        · exact absurd h' (by decide +kernel)
    · cases h
  | map s' es | set s' es | list s' es =>
    have hs' : s' = s := by
      first
        | (obtain ⟨_, _, _, _, _, _, _, h⟩ := sortOf_mapS_fwd h; exact h.symm)
        | (obtain ⟨_, _, _, _, _, h⟩ := sortOf_setS.mp h; exact h.symm)
        | (obtain ⟨_, _, _, _, h⟩ := sortOf_listS.mp h; exact h.symm)
    subst hs'
    rcases hs with rfl | rfl
    · rw [Semantics.sortOf, coll_own.1] at h; cases h
    · rw [Semantics.sortOf, coll_own.2] at h; cases h

/-- **No value has sort Empty.** -/
theorem no_E (v : GroundTerm) : c.sortOf v ≠ some E := fun h => by
  obtain ⟨k, hk, hr, -⟩ := sortOf_own (.inr rfl) h
  have := List.all_eq_true.mp ctors_E k hk
  simp [hr] at this

/-- **`u` is U's only value.** -/
theorem u_only {v : GroundTerm} (h : c.sortOf v = some U) : v = .ctor uL [] := by
  obtain ⟨k, hk, hr, ts, rfl, hts⟩ := sortOf_own (.inl rfl) h
  have := List.all_eq_true.mp ctors_U k hk
  simp only [hr, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at this
  obtain ⟨hn, ha⟩ := this
  rw [ha] at hts
  cases ts with
  | nil => rw [hn]
  | cons t ts =>
    simp only [Semantics.sortsOf] at hts
    split at hts <;> cases hts

/-! ## C1: a matched clause of the smallest priority with a variable of a sort without a value -/

/-- A clause without a `requires`, of the precondition `.top`, that some σ over its patterns and
conditions matches does not fail. -/
theorem not_fails {c : Semantics} {vs : List GroundTerm} {cl : Clause} {σ : Subst}
    (hσ : c.WellSortedAt cl.vars cl.leftVars σ) (hm : PatVals c σ cl.pats vs) (hreq : cl.req = none)
    (hpre : cl.pre = .top) : ¬ Fails c vs cl := by
  intro h
  cases h with
  | intro h =>
    cases h σ hσ hm with
    | intro ht _ _ => rw [hreq] at ht; cases ht
    | pre h => rw [hpre] at h; exact absurd (Holds.top_eq h) (by simp)

/-- No σ is well sorted on the variables of a clause that has one of a sort without a value. -/
theorem not_wellSorted {c : Semantics} {cl : Clause} {i : Nat} {s : Srt} (hi : cl.vars[i]? = some s)
    (hno : ∀ v, c.sortOf v ≠ some s) (σ : Subst) : ¬ c.WellSorted cl.vars σ := by
  intro h
  obtain ⟨v, -, hv⟩ := h i s hi
  exact hno v hv

/-- **C1.** A clause that is not `aside`, of a smaller priority than its function's other clauses,
without a `requires`, of the precondition `.top`, with a variable of a sort without a value, matched at `vs` by a σ well sorted
on its patterns and conditions: `Eval` has no result at `vs`. -/
theorem no_result {c : Semantics} {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl : Clause} {σ : Subst}
    {i : Nat} {s : Srt}
    (hfn : c.lookupFn f = some fn) (hcl : cl ∈ fn.clauses) (hna : cl.aside = false)
    (hlow : ∀ cl' ∈ fn.clauses, cl' ≠ cl → cl.prio < cl'.prio)
    (hi : cl.vars[i]? = some s) (hno : ∀ v, c.sortOf v ≠ some s)
    (hσ : c.WellSortedAt cl.vars cl.leftVars σ) (hm : PatVals c σ cl.pats vs) (hreq : cl.req = none)
    (hpre : cl.pre = .top) : ¬ ∃ r, Eval c f vs r := by
  have hnf := not_fails hσ hm hreq hpre
  rintro ⟨r, h⟩
  cases h with
  | @clauseEx _ fn' _ cl' σ' _ hfn' hmem hσ' _ _ _ hprio _ _ _ _ _ =>
    have hE : fn' = fn := Option.some.inj (hfn'.symm.trans hfn)
    subst hE
    by_cases hc : cl' = cl
    · subst hc; exact not_wellSorted hi hno σ' hσ'
    · exact hnf (hprio cl hcl hna (hlow cl' hmem hc))
  | @exNone _ fn' _ cl' σ' hfn' hmem _ _ _ _ _ hprio hsome _ =>
    have hE : fn' = fn := Option.some.inj (hfn'.symm.trans hfn)
    subst hE
    by_cases hc : cl' = cl
    · subst hc
      obtain ⟨σ₁, -, hσ₁⟩ := hsome
      exact not_wellSorted hi hno σ₁ hσ₁
    · exact hnf (hprio cl hcl hna (hlow cl' hmem hc))
  | @clause _ fn' _ cl' σ' _ hfn' hmem hσ' hmatch hreq' _ hprio _ hrhs hens _ =>
    have hE : fn' = fn := Option.some.inj (hfn'.symm.trans hfn)
    subst hE
    by_cases hc : cl' = cl
    · subst hc; exact not_wellSorted hi hno σ' hσ'
    · exact hnf (hprio cl hcl hna (hlow cl' hmem hc))
  | @rest _ fn' _ hfn' hnone =>
    have hE : fn' = fn := Option.some.inj (hfn'.symm.trans hfn)
    subst hE
    exact hnf (hnone cl hcl)
  | @ensFails _ fn' _ cl' σ' t w hfn' hmem hσ' hmatch hreq' _ hprio _ ht he hw =>
    have hE : fn' = fn := Option.some.inj (hfn'.symm.trans hfn)
    subst hE
    by_cases hc : cl' = cl
    · subst hc; exact not_wellSorted hi hno σ' hσ'
    · exact hnf (hprio cl hcl hna (hlow cl' hmem hc))

theorem hfnE : c.lookupFn fEL = some fE := rfl

/-- **`fE() = g(Y:Empty)` has no result**: C1 at `clE`, the only clause of `fE`. -/
theorem fE_none : ¬ ∃ r, Eval c fEL [] r :=
  no_result (σ := []) (i := 0) hfnE (List.Mem.head _) rfl
    (fun cl' h hne => by simp only [fE, List.mem_singleton] at h; exact absurd h hne)
    rfl no_E (fun i hi => by rw [right_only.2.2.1] at hi; cases hi) .nil rfl rfl

/-! ## `clE` beside `fEA() = a` at one priority: `Eval` gives `a`, and `FnHyp` holds -/

/-- `fEA` alone. -/
def cEA : Semantics := { c with fns := [fEA] }

kernel_rfl sortOf_cEA : cEA.sortOf = c.sortOf
theorem no_E' (v : GroundTerm) : cEA.sortOf v ≠ some E := by rw [sortOf_cEA]; exact no_E v
theorem hfnEA : cEA.lookupFn fEAL = some fEA := rfl
theorem ws_nil : cEA.WellSorted [] [] := fun i s h => by simp at h

/-- A clause with a variable of a sort without a value applies under no substitution. -/
theorem not_appliesAt {c : Semantics} {cl : Clause} {i : Nat} {s : Srt} (hi : cl.vars[i]? = some s)
    (hno : ∀ v, c.sortOf v ≠ some s) (σ : Subst) (vs : List GroundTerm) : ¬ cl.AppliesAt c σ vs := by
  rintro ⟨h, -⟩
  obtain ⟨v, -, hv⟩ := h i s hi
  exact hno v hv

/-- Such a clause is coherent with every clause, on either side, and so match independent. -/
theorem coherent_left {c : Semantics} {cl : Clause} {i : Nat} {s : Srt} (hi : cl.vars[i]? = some s)
    (hno : ∀ v, c.sortOf v ≠ some s) (cl' : Clause) : Coherent c cl cl' :=
  fun vs σ _ ha => absurd ha (not_appliesAt hi hno σ vs)

theorem coherent_right {c : Semantics} {cl : Clause} {i : Nat} {s : Srt} (hi : cl.vars[i]? = some s)
    (hno : ∀ v, c.sortOf v ≠ some s) (cl' : Clause) : Coherent c cl' cl :=
  fun vs _ σ' _ ha => absurd ha (not_appliesAt hi hno σ' vs)

/-- **A matched clause with a valueless variable does not stop a clause of the same or a smaller
priority from deciding**: `Eval.clause` of the other clause reads `Fails` only of the clauses of a
strictly smaller priority that are not `aside`. -/
theorem peer_decides {c : Semantics} {f : Sym} {fn : Fn} {vs : List GroundTerm} {cl' : Clause} {σ : Subst}
    {r : Option GroundTerm}
    (hfn : c.lookupFn f = some fn) (hmem : cl' ∈ fn.clauses) (ha : cl'.AppliesAt c σ vs)
    (hprio : ∀ cl'' ∈ fn.clauses, cl''.aside = false → cl''.prio < cl'.prio → Fails c vs cl'')
    (hens : cl'.ens = none) (hrhs : EvalTerm c σ cl'.rhs r) (hx : cl'.exs = [] := by rfl)
    (hpost : Holds c cl'.vars.length σ cl'.post true := by exact .top) : Eval c f vs r :=
  Eval.clause hfn hmem ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 hprio hx hrhs (fun t ht => by rw [hens] at ht; cases ht) hpost

theorem eval_aTerm : EvalTerm cEA [] clA.rhs (some (.ctor aL [])) :=
  EvalTerm.ctor (rs := []) (by decide +kernel) .nil

/-- **`fEA()` is `a`**: `clA` decides, no clause being of a smaller priority. -/
theorem fEA_a : Eval cEA fEAL [] (some (.ctor aL [])) :=
  peer_decides hfnEA (List.Mem.tail _ (List.Mem.head _)) ⟨ws_nil, .nil, (fun t h => by cases h), .top⟩
    (fun cl' h _ hlt => by
      simp only [fEA, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> simp [clE, clA] at hlt)
    rfl eval_aTerm

/-- `clA` has no variable: it is match independent. -/
theorem clA_coherent : Coherent cEA clA clA := fun _ _ _ _ _ _ _ _ _ _ =>
  .inl ⟨rfl, rfl, rfl, rfl, fun i hi => by simp [clA, varOccs, varOccsList] at hi, fun t ht => by cases ht⟩

theorem sortsOf_nil {vs : List GroundTerm} (h : cEA.sortsOf vs = some []) : vs = [] := by
  cases vs with
  | nil => rfl
  | cons v vs => simp only [Semantics.sortsOf] at h; split at h <;> cases h

/-- **`FnHyp` of `cEA`, by hand**: `fEA` has a result (`a`) at its one argument list, is not
`[total]`, its clauses agree (each pair holds `clE`, coherent with every clause), each clause is
match independent, no clause needs a witness, and there is no parameter. -/
theorem fnHyp_cEA : FnHyp cEA := by
  refine ⟨fun fn hfn vs hvs => ?_, fun fn hfn ht => ?_, fun fn hfn => ?_, fun fn hfn cl hcl => ?_, ?_, ?_⟩
  · simp only [cEA, List.mem_singleton] at hfn
    subst hfn
    rw [sortsOf_nil hvs]
    exact ⟨_, fEA_a⟩
  · simp only [cEA, List.mem_singleton] at hfn
    subst hfn; cases ht
  · simp only [cEA, List.mem_singleton] at hfn
    subst hfn
    intro cl cl' hp _
    simp only [fEA, pairs, List.map_cons, List.map_nil, List.nil_append, List.cons_append,
      List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hp
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨coherent_left (i := 0) rfl no_E' _, coherent_right (i := 0) rfl no_E' _⟩
  · simp only [cEA, List.mem_singleton] at hfn
    subst hfn
    simp only [fEA, List.mem_cons, List.not_mem_nil, or_false] at hcl
    rcases hcl with rfl | rfl
    · exact (matchIndependent_iff_noExs rfl).mpr (coherent_left (i := 0) rfl no_E' _)
    · exact (matchIndependent_iff_noExs rfl).mpr clA_coherent
  · exact openDecided_of_plain (fun r hr => by cases hr) (by decide +kernel)
  · exact openLaws_of_plain (fun k hk => by cases hk)

/-- `rightValued` fails at `cEA` (`clE`), and `RightHeld` is false there: it is the class the
deciders do not derive `FnHyp` for, while `FnHyp` holds. -/
theorem not_rightHeld_cEA : cEA.rightValued = false ∧ ¬ cEA.RightHeld :=
  ⟨by decide +kernel, fun h => by
    rcases h fEA (List.Mem.head _) clE (List.Mem.head _) 0 E rfl with h | ⟨v, hv⟩
    · rw [right_only.2.2.1] at h; cases h
    · exact no_E' v hv⟩

/-! ## `fU() = h(Y:U)`: one value of U -/

theorem hfnU : c.lookupFn fUL = some fU := rfl

def σu : Subst := [(0, .ctor uL [])]

theorem ws_u : c.WellSorted clU.vars σu := fun i s hs => by
  cases i with
  | zero =>
    simp only [clU, List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨_, rfl, by decide +kernel⟩
  | succ i => simp [clU] at hs

/-- **`fU()` is `h(u)`.** -/
theorem fU_hu : Eval c fUL [] (some (.ctor hL [.ctor uL []])) :=
  peer_decides (σ := σu) hfnU (List.Mem.head _) ⟨ws_u, .nil, (fun t h => by cases h), .top⟩
    (fun cl' h _ hlt => by simp only [fU, List.mem_singleton] at h; subst h; simp at hlt)
    rfl (EvalTerm.ctor (rs := [some (.ctor uL [])]) (by decide +kernel) (.cons .var .nil))

/-- **`clU` is match independent**: every σ well sorted on its variables gives Y the value `u`
(`u_only`), so two matches are one instance of the right side. -/
theorem matchIndependent_U : MatchIndependent c clU := by
  refine ⟨?_, fun hne => absurd rfl hne⟩
  intro vs σ σ' ha ha' _ _ _ _ _
  refine .inl ⟨rfl, rfl, rfl, rfl, fun i hi => ?_, fun t ht => by cases ht⟩
  simp only [clU, varOccs, varOccsList, List.append_nil, List.mem_singleton] at hi
  subst hi
  obtain ⟨v, hv, hs⟩ := ha.1 0 U rfl
  obtain ⟨v', hv', hs'⟩ := ha'.1 0 U rfl
  rw [hv, hv', u_only hs, u_only hs']

/-! ## `fI() = k(Y:Int)`: two values of Int, two results -/

def σ0 : Subst := [(0, .dv Srt.int (.int 0))]
def σ1 : Subst := [(0, .dv Srt.int (.int 1))]

theorem ws_int (n : Int) : c.WellSorted clI.vars [(0, .dv Srt.int (.int n))] := fun i s hs => by
  cases i with
  | zero =>
    simp only [clI, List.getElem?_cons_zero, Option.some.injEq] at hs
    subst hs
    exact ⟨_, rfl, by simp [Semantics.sortOf, show dvOK c.lib Srt.int (.int n) = true from rfl]⟩
  | succ i => simp [clI] at hs

theorem k_ctor : c.isCtor kL = true := by decide +kernel

/-- `k(Y)` has one result under each σ: `k` is a constructor. -/
theorem hdet_k (σ : Subst) : HDet c σ clI.rhs := by
  intro u hu r r' h1 h2
  simp only [clI, subterms, subtermsList, List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · cases h1 with
    | ctor _ hts1 =>
      cases h2 with
      | ctor _ hts2 =>
        cases hts1 with
        | cons h1' hs1 =>
          cases hts2 with
          | cons h2' hs2 =>
            cases hs1; cases hs2
            rw [EvalTerm.var_inv h1', EvalTerm.var_inv h2']
      | hook h => rw [k_ctor] at h; cases h
      | param h => rw [k_ctor] at h; cases h
      | call h => rw [k_ctor] at h; cases h
      | callUndef h => rw [k_ctor] at h; cases h
      | ovl h => rw [k_ctor] at h; cases h
      | ovlFn h => rw [k_ctor] at h; cases h
    | hook h => rw [k_ctor] at h; cases h
    | param h => rw [k_ctor] at h; cases h
    | call h => rw [k_ctor] at h; cases h
    | callUndef h => rw [k_ctor] at h; cases h
    | ovl h => rw [k_ctor] at h; cases h
    | ovlFn h => rw [k_ctor] at h; cases h
  · rw [EvalTerm.var_inv h1, EvalTerm.var_inv h2]

theorem hfnI : c.lookupFn fIL = some fI := rfl

theorem eval_k (n : Int) :
    EvalTerm c [(0, .dv Srt.int (.int n))] clI.rhs (some (.ctor kL [.dv Srt.int (.int n)])) :=
  EvalTerm.ctor (rs := [some (.dv Srt.int (.int n))]) k_ctor (.cons .var .nil)

/-- **`clI` is not match independent**: Y = 0 and Y = 1 both decide `fI()`, with the results `k(0)`
and `k(1)`. -/
theorem not_matchIndependent_I : ¬ MatchIndependent c clI := fun h => by
  have ha : ∀ n : Int, clI.AppliesAt c [(0, .dv Srt.int (.int n))] [] :=
    fun n => ⟨ws_int n, .nil, (fun t h => by cases h), .top⟩
  have hdec : ∀ n : Int, clI.Decides c fI [(0, .dv Srt.int (.int n))] [] := fun n =>
    ⟨ha n, fun cl' h _ hlt => by simp only [fI, List.mem_singleton] at h; subst h; simp at hlt⟩
  rcases h.1 [] σ0 σ1 (ha 0) (ha 1) (fun t h => by cases h) (fun _ _ => hdet_k σ0) (fun _ t h => by cases h)
      (fun hne => absurd rfl hne) ⟨fIL, fI, hfnI, List.Mem.head _, List.Mem.head _, hdec 0, hdec 1⟩ with ⟨-, -, -, -, hv, -⟩ | hr
  · have := hv 0 (by simp [clI, varOccs, varOccsList])
    simp [σ0, σ1] at this
  · have := hr _ _ (.inl ⟨rfl, .inl ⟨(fun t h => by cases h), .top, eval_k 0⟩⟩)
      (.inl ⟨rfl, .inl ⟨(fun t h => by cases h), .top, eval_k 1⟩⟩)
    simp at this

/-- info: 'KCore.RightOnlyTest.rightHeld_cV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rightHeld_cV
/-- info: 'KCore.RightOnlyTest.fE_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fE_none
/-- info: 'KCore.RightOnlyTest.fEA_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fEA_a
/-- info: 'KCore.RightOnlyTest.fnHyp_cEA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fnHyp_cEA
/-- info: 'KCore.RightOnlyTest.not_rightHeld_cEA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms not_rightHeld_cEA
/-- info: 'KCore.RightOnlyTest.fU_hu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms fU_hu
/-- info: 'KCore.RightOnlyTest.matchIndependent_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms matchIndependent_U
/-- info: 'KCore.RightOnlyTest.not_matchIndependent_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms not_matchIndependent_I

end KCore.RightOnlyTest
