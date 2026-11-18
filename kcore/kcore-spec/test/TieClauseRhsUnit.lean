/-
  The fixture e2-clause-rhs-unit: `rule f() => h(Y:U) [unboundVariables(Y)]` (`U ::= "u"`,
  `T ::= h(U)`, `T ::= f() [function]`). The text is `f2-examples/rhsunit.kompile.kore`, the kompiled
  text of `test/constructs/fixtures/e2-clause-rhs-unit`: an equation whose right side holds a
  variable its left side does not bind, of a sort with a value, as e2-clause-rhs-int's
  `f() => c(Y:Int)`, here of a sort with one value. Run from the package root:
  `lake env lean -j1 test/TieClauseRhsUnit.lean`. Every statement is on the literal `defn`, for every
  interpretation H; nothing reads `Parse.parse` or `emit`.

  - The reader's semantics is `coreOK` and `rightValued`; `f` is its one function, and the fact the
    package names as owed for `f`'s clause (`matchObligationsL`) is its `MatchIndependent`; no rule
    and no clause owes a condition (`named`).
  - U has one value, `u` (`u_only`): the one constructor whose result is U is `u`, of no argument,
    and no overload, open generator, subsort, literal or collection has the sort U (`oneValue`).
  - The owed fact holds (`matchY`): every substitution under which the clause applies gives Y the
    value `u`, so two matches of the clause are one instance of its right side.
-/
import KcoreSpec

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace KCore.TieClauseRhsUnit

open KCore

/-- **The sort `e` has one value, the constant `u`**, when every constructor whose result is `e` is
`u` of no argument, and no overload, open generator or subsort ends there, no literal is of it and
it is no collection sort. -/
theorem oneValue {c : Semantics} {e : Srt} {u : Sym}
    (hctor : c.ctorSigs.all (fun k => k.result != e || (k.name == u && k.args.isEmpty)) = true)
    (hovl : c.ovls = []) (hraw : ∀ k ∈ c.params, k.raw = false)
    (hsub : c.subsorts.all (fun p => p.2 != e) = true) (hcoll : c.collOf e = none)
    (hcarr : c.lib.carriers.all (·.1 != e) = true)
    (hlit : (e != Srt.int && e != Srt.bool && e != Srt.kconfigVar && e != Srt.string && e != Srt.bytes &&
      e != Srt.float && !c.lib.tokenSorts.contains e && !c.lib.byteSorts.contains e) = true)
    {v : GroundTerm} (h : c.sortOf v = some e) : v = .ctor u [] := by
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
      · rename_i hts
        have hfk := List.find?_some (by rw [← lookupSig_eq]; exact hk')
        have hm := List.mem_of_find?_eq_some (by rw [← lookupSig_eq]; exact hk')
        simp only [beq_iff_eq] at hfk hts
        subst hfk
        have := List.all_eq_true.mp hctor k hm
        rw [Option.some.inj h] at this
        simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at this
        obtain ⟨hn, ha⟩ := this
        rw [ha] at hts
        cases ts with
        | nil => rw [hn]
        | cons t ts =>
          simp only [Semantics.sortsOf] at hts
          split at hts <;> cases hts
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
    exfalso
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

definition_of defn from "f2-examples/rhsunit.kompile.kore"

noncomputable abbrev c : Semantics := defn.sem
noncomputable abbrev cH (H : HookParams) : Semantics := c.withHooks H

def fS : Sym := 388
def hS : Sym := 386
def uS : Sym := 387
def uT : Srt := 33

/-- The symbols and the sort the clause names. -/
theorem names : c.symName fS = "Lblf" ∧ c.symName hS = "Lblh" ∧ c.symName uS = "Lblu" ∧
    c.sortName uT = "U" := by
  decide +kernel

/-- The semantics is `coreOK` and `rightValued`; the one function is `f`, and the fact owed of its
clause is match independence (`matchObligationsL`); no rule and no clause owes a condition. -/
theorem named : c.coreOK = true ∧ c.rightValued = true ∧ (c.fns.map (·.label)) = [fS] ∧
    c.matchObligationsL = [(fS, 0)] ∧ c.owedRules = [] ∧ c.owedClauses = [] := by
  decide_cheap

/-! ## U has one value -/

/-- What `oneValue` asks of U. -/
theorem oneU : c.ctorSigs.all (fun k => k.result != uT || (k.name == uS && k.args.isEmpty)) = true ∧
    c.ovls = [] ∧ c.params.all (!·.raw) = true ∧ c.subsorts.all (fun p => p.2 != uT) = true ∧
    c.collOf uT = none ∧ c.lib.carriers.all (·.1 != uT) = true ∧
    (uT != Srt.int && uT != Srt.bool && uT != Srt.kconfigVar && uT != Srt.string && uT != Srt.bytes &&
      uT != Srt.float && !c.lib.tokenSorts.contains uT && !c.lib.byteSorts.contains uT) = true := by
  decide +kernel

theorem noRaw : ∀ k ∈ c.params, k.raw = false := fun k hk => by
  have := List.all_eq_true.mp oneU.2.2.1 k hk; simpa using this

theorem sortOfH (H : HookParams) : (cH H).sortOf = c.sortOf := Semantics.sortOf_withHooks c H noRaw

/-- **`u` is U's only value, for every H.** -/
theorem u_only (H : HookParams) {v : GroundTerm} (h : (cH H).sortOf v = some uT) : v = .ctor uS [] := by
  rw [sortOfH H] at h
  exact oneValue oneU.1 oneU.2.1 noRaw oneU.2.2.2.1 oneU.2.2.2.2.1 oneU.2.2.2.2.2.1 oneU.2.2.2.2.2.2 h

/-! ## The function and its clause -/

noncomputable def fF : Fn := c.fns[0]'(by decide +kernel)
noncomputable def clY : Clause := fF.clauses[0]'(by decide +kernel)

/-- `f() => h(Y:U)`: the clause `matchObligationsL` names (`f`'s clause 0), one variable, of U,
which its patterns do not bind, no `ensures`, no existential variable. -/
theorem clY_shape : fF.label = fS ∧ clY.vars = [uT] ∧ clY.ens.isNone = true ∧ clY.exs = [] := by
  decide +kernel

theorem clY_rhs : clY.rhs = .app hS [.var 0] := by rfl
theorem clY_ens : clY.ens = none := Option.isNone_iff_eq_none.mp clY_shape.2.2.1
theorem clY_exs : clY.exs = [] := clY_shape.2.2.2

/-! ## The owed fact, proved -/

/-- **The fact owed of the clause holds, for every H**: `f() => h(Y)` is match independent. Every
substitution under which the clause applies is well sorted on its variables, so gives Y a value of
U, which is `u` (`u_only`): two matches are one instance of the right side. -/
theorem matchY (H : HookParams) : MatchIndependent (cH H) clY := by
  refine ⟨?_, fun hne => absurd clY_exs hne⟩
  intro vs σ σ' ha ha' _ _ _ _ _
  refine .inl ⟨clY_exs, clY_exs, rfl, rfl, fun i hi => ?_, fun t ht => by rw [clY_ens] at ht; cases ht⟩
  rw [clY_rhs] at hi
  simp only [varOccs, varOccsList, List.append_nil, List.mem_singleton] at hi
  subst hi
  have hv0 : clY.vars[0]? = some uT := by rw [clY_shape.2.1]; rfl
  obtain ⟨v, hv, hs⟩ := (wellSortedAt_univ clY_exs).mp ha.1 0 uT hv0
  obtain ⟨v', hv', hs'⟩ := (wellSortedAt_univ clY_exs).mp ha'.1 0 uT hv0
  rw [hv, hv', u_only H hs, u_only H hs']

end KCore.TieClauseRhsUnit

#check @KCore.TieClauseRhsUnit.named
#check @KCore.TieClauseRhsUnit.u_only
#check @KCore.TieClauseRhsUnit.matchY
#print axioms KCore.TieClauseRhsUnit.oneValue
#print axioms KCore.TieClauseRhsUnit.named
#print axioms KCore.TieClauseRhsUnit.matchY
