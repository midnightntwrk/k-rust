/-
  The contrast of the priority attribute on the two competitor fixtures of the pairs equation
  `priority` x `requires` and `priority` x `[total]` (C3): the same two equations with no
  `priority` attribute, both of the default priority 50. The semantics is hand-built (a small
  core with the configuration's cells, as test/AgreeInst.lean's); its clauses are the fixtures'
  clauses with the priority 40 replaced by 50: test/C3EqReqPrioComp.lean and
  test/C3EqPrioTotalComp.lean check by kernel that the fixtures' function has exactly the clauses
  `clA` (`clT`) and `clB` below with `prio := 40` on the first (`clauses_eq` there).
  Run from the package root: `lake env lean -j1 test/C3EqPrioFlat.lean`.

  1. c3-eq-req-prio-comp without the attribute: `f(X) = X requires X >Int 0` beside `f(_) = 0`.
     Both apply at 5 (the `requires` by the graph of `>Int` at (5, 0)) with the results 5 and 0,
     so the two clauses, of one priority, compete and are not coherent: `ClausesAgree` is false
     (`not_agree_req`). The agreement decider names the function (`named`): its agreement is an
     owed fact, and it is false.
  2. c3-eq-prio-total-comp without the attribute: `f(X) = X` beside `f(_) = 0`; the same at 5
     (`not_agree_tot`).
  3. With the attribute (the first clause of priority 40): the two clauses do not compete
     (`ClausesAgree.not_compete`), so `ClausesAgree` asks nothing of the pair and holds
     (`agree_req_prio`, `agree_tot_prio`).
  So the attribute, with no change to any pattern, is what turns an owed agreement that is false
  into a function with one value at 5; which value is the order of the reading (the clause of the
  smaller number first), checked by the expectations `f_5` of the two fixtures' tie files.
-/
import KcoreSpec.AgreeInst
import KcoreSpec.CoreDecide

set_option autoImplicit false

namespace KCore.C3EqPrioFlat

open KCore KCore.Det

def cellSorts : List Srt := [Srt.top, Srt.topFrag, nRegSorts, nRegSorts + 1, Srt.counter, Srt.counterOpt]
def cellCtors : List CtorSig :=
  [⟨topLabel, [nRegSorts, Srt.counter], Srt.top⟩, ⟨topFragLabel, [nRegSorts + 1, Srt.counterOpt], Srt.topFrag⟩,
   ⟨nRegSyms + 50, [Srt.k], nRegSorts⟩, ⟨nRegSyms + 51, [], nRegSorts + 1⟩,
   ⟨counterLabel, [Srt.int], Srt.counter⟩, ⟨noCounter, [], Srt.counterOpt⟩]
def cellSubsorts : List (Srt × Srt) := [(nRegSorts, nRegSorts + 1), (Srt.counter, Srt.counterOpt)]

def core (fns : List Fn) : Semantics where
  lib := { sortsBelowKItem := [Srt.int, Srt.bool] }
  sortNames := []
  symNames := []
  userSorts := cellSorts
  ctors := cellCtors
  fns := fns
  userSubsorts := cellSubsorts
  pgmSort := Srt.k
  rules := []

def fR : Sym := nRegSyms + 120
def fT : Sym := nRegSyms + 121

/-- `f(X) = X requires X >Int 0`, c3-eq-req-prio-comp's equation of priority 40, here of 50. -/
def clA : Clause := ⟨[Srt.int], [.var 0], some (.app intGt [.var 0, .dv Srt.int (.int 0)]), .var 0, none, 50, false, [], .top, .top⟩
/-- `f(X) = X`, c3-eq-prio-total-comp's equation of priority 40, here of 50. -/
def clT : Clause := ⟨[Srt.int], [.var 0], none, .var 0, none, 50, false, [], .top, .top⟩
/-- `f(_) = 0`, of the default priority in both fixtures. -/
def clB : Clause := ⟨[Srt.int], [.var 0], none, .dv Srt.int (.int 0), none, 50, false, [], .top, .top⟩

def fnR : Fn := ⟨fR, [Srt.int], Srt.int, [clA, clB], false⟩
def fnT : Fn := ⟨fT, [Srt.int], Srt.int, [clT, clB], true⟩

def flat : Semantics := core [fnR, fnT]

theorem flat_sorted : flat.sortedOK = true ∧ flat.srReady = true ∧ flat.matchReady = true := by decide_cheap

/-- **The agreement decider names both functions**: their agreement is an owed fact. -/
theorem named : flat.agreeObligationsI = [fR, fT] := by decide +kernel

def v5 : GroundTerm := .dv Srt.int (.int 5)
def σ5 : Subst := [(0, v5)]

theorem ws5 (cl : Clause) (hv : cl.vars = [Srt.int]) : flat.WellSorted cl.vars σ5 := by
  intro i s hi
  rw [hv] at hi
  match i, hi with
  | 0, hi => simp only [List.getElem?_cons_zero, Option.some.injEq] at hi; subst hi
             exact ⟨v5, rfl, by decide +kernel⟩
  | _ + 1, hi => simp at hi

theorem pv5 (cl : Clause) (hp : cl.pats = [.var 0]) : PatVals flat σ5 cl.pats [v5] := by
  rw [hp]; exact .cons (.var rfl) .nil

/-- `5 >Int 0` is `true`. -/
theorem gt5 : EvalTerm flat σ5 (.app intGt [.var 0, .dv Srt.int (.int 0)]) (some (bool true)) :=
  .hook (by decide +kernel) rfl (.cons .var (.cons .dv .nil)) (fun vs h => by cases h; rfl) (fun h => by cases h)

/-- No clause of either function has a smaller priority than another. -/
theorem nolow (fn : Fn) (hf : fn.clauses.all (·.prio == 50) = true) (cl : Clause) (hc : cl.prio = 50) :
    ∀ cl' ∈ fn.clauses, cl'.aside = false → cl'.prio < cl.prio → Fails flat [v5] cl' := fun cl' h _ hlt => by
  have : cl'.prio = 50 := by simpa using List.all_eq_true.mp hf cl' h
  rw [hc, this] at hlt; exact absurd hlt (Nat.lt_irrefl _)

/-- A plain term has one result under every match. -/
theorem hdet (t : Term) (h : flat.plainTerm t = true) : HDet flat σ5 t :=
  fun _ hu => plain_fun (plain_subterms h hu)

theorem appA : clA.AppliesAt flat σ5 [v5] :=
  ⟨ws5 clA rfl, pv5 clA rfl, (fun t ht => by cases ht; exact gt5), .top⟩
theorem appT : clT.AppliesAt flat σ5 [v5] := ⟨ws5 clT rfl, pv5 clT rfl, (fun _ ht => by cases ht), .top⟩
theorem appB : clB.AppliesAt flat σ5 [v5] := ⟨ws5 clB rfl, pv5 clB rfl, (fun _ ht => by cases ht), .top⟩

/-- **Without the attribute, `ClausesAgree` of c3-eq-req-prio-comp's function is false**: at 5 both
clauses decide, `f(X) = X requires X >Int 0` with 5 and `f(_) = 0` with 0. -/
theorem not_agree_req : ¬ ClausesAgree flat fnR := by
  intro h
  rcases (h clA clB (by simp [fnR, pairs]) (.inl rfl)).2 [v5] _ _ appB appA
      (fun _ ht => by cases ht) (fun _ _ => hdet _ (by decide +kernel)) (fun _ _ ht => by cases ht) (fun hne => absurd rfl hne)
      ⟨fR, fnR, rfl, by simp [fnR], by simp [fnR], ⟨appB, nolow fnR rfl clB rfl⟩, ⟨appA, nolow fnR rfl clA rfl⟩⟩
    with ⟨-, -, hr, -⟩ | hr
  · simp [clA, clB] at hr
  · have := hr _ _ (.inl ⟨rfl, .inl ⟨(fun _ ht => by cases ht), .top, .dv⟩⟩)
      (.inl ⟨rfl, .inl ⟨(fun _ ht => by cases ht), .top, .var⟩⟩)
    simp [σ5, v5] at this

/-- **Without the attribute, `ClausesAgree` of c3-eq-prio-total-comp's function is false**: at 5
`f(X) = X` gives 5 and `f(_) = 0` gives 0. -/
theorem not_agree_tot : ¬ ClausesAgree flat fnT := by
  intro h
  rcases (h clT clB (by simp [fnT, pairs]) (.inl rfl)).1 [v5] _ _ appT appB
      (fun _ ht => by cases ht) (fun _ _ => hdet _ (by decide +kernel))
      (fun _ _ ht => by cases ht) (fun hne => absurd rfl hne)
      ⟨fT, fnT, rfl, by simp [fnT], by simp [fnT], ⟨appT, nolow fnT rfl clT rfl⟩, ⟨appB, nolow fnT rfl clB rfl⟩⟩
    with ⟨-, -, hr, -⟩ | hr
  · simp [clT, clB] at hr
  · have := hr _ _ (.inl ⟨rfl, .inl ⟨(fun _ ht => by cases ht), .top, .var⟩⟩)
      (.inl ⟨rfl, .inl ⟨(fun _ ht => by cases ht), .top, .dv⟩⟩)
    simp [σ5, v5] at this

/-- The same functions with the first clause of priority 40, as the fixtures write it. -/
def fnR40 : Fn := ⟨fR, [Srt.int], Srt.int, [{ clA with prio := 40 }, clB], false⟩
def fnT40 : Fn := ⟨fT, [Srt.int], Srt.int, [{ clT with prio := 40 }, clB], true⟩

theorem agree_of_two (s : Semantics) (fn : Fn) (a b : Clause) (hc : fn.clauses = [a, b])
    (hn : (a.prio != b.prio && !a.aside && !b.aside) = true) : ClausesAgree s fn := by
  intro cl cl' hp hpr
  rw [hc] at hp
  simp only [pairs, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
    Prod.mk.injEq, List.not_mem_nil, or_false] at hp
  obtain ⟨rfl, rfl⟩ := hp
  exact absurd hpr (not_compete hn)

/-- **With the attribute, `ClausesAgree` holds**: the two clauses are of different priorities and
neither is `aside`, so they do not compete. -/
theorem agree_req_prio (s : Semantics) : ClausesAgree s fnR40 := agree_of_two s fnR40 _ _ rfl (by decide)
theorem agree_tot_prio (s : Semantics) : ClausesAgree s fnT40 := agree_of_two s fnT40 _ _ rfl (by decide)

end KCore.C3EqPrioFlat

#print axioms KCore.C3EqPrioFlat.named
#print axioms KCore.C3EqPrioFlat.not_agree_req
#print axioms KCore.C3EqPrioFlat.not_agree_tot
#print axioms KCore.C3EqPrioFlat.agree_req_prio
#print axioms KCore.C3EqPrioFlat.agree_tot_prio
