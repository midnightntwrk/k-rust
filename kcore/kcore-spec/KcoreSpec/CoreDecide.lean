/-
  KCore, checked layer: `coreOK`, `faithCoreOK` and `sortedOK` decided conjunct by conjunct, each
  conjunct a kernel decision of its own, the three conjuncts of `faithCoreOK` that read names
  (`namesNumbered`, `namesApartK`, `itesApart`) decided on the names' codes (NameCodes.lean), the
  codes of the registry's names computed once, here (`regSymCodesCD`, `regSortCodesCD`).

  A single kernel decision of `coreOK` keeps every reduction it makes until it ends, so its memory is
  the sum of its conjuncts'. `namesApartK` and `itesApart` compare every two entries of `kernelSyms`,
  the interpreted hooks among them, by their names, so even for a semantics with few symbols of its
  own they read the names of the whole registry once per pair. Decided apart, the memory is that of
  the costliest conjunct; on codes, each name is read once.

  `decide_namesNumbered`, `decide_namesApartK` and `decide_itesApart` close those three conjuncts on
  codes. `namesApartC` asks in addition that every symbol of `kernelSyms` be numbered and listed
  once, which a semantics may not meet while it meets `namesApartK`; `decide_namesApartK` then
  decides `namesApartFast` (`namesApartK_of_fast`). `decide_leafCD` closes a goal `b = true` by
  the decider of its head among those three, any other goal by `decide +kernel`.
  `decide_sortedOK`, `decide_faithCoreOK`, `decide_coreOK` and `decide_wf` split their goal into its conjuncts
  and close each by `decide_leafCD`; `decide_cheap` splits a conjunction (of propositions or of Booleans) and picks among all of these
  by the goal's head.
  `decide_map_blocks n k` decides an equation of two mapped lists by blocks of n entries.
  They fail where the kernel refutes a conjunct, and they prove no other statement than the goal.
-/
import KcoreSpec.NameCodes

set_option autoImplicit false

open Lean Elab Term in
/-- The list of the codes (`strCode`) of the names in `l`, computed when the term is elaborated
and written as numerals. -/
elab "codes_of%" l:term : term => do
  let e ← instantiateMVars (← elabTerm l (some (mkApp (mkConst ``List [0]) (mkConst ``String))))
  let v ← unsafe Meta.evalExpr (List String) (mkApp (mkConst ``List [0]) (mkConst ``String)) e
  return toExpr (v.map KoreAML.Distinct.strCode)

namespace KCore

open KoreAML.Distinct Faithful Faithful.Model

variable {c : Semantics}

/-! ## The names' codes, the registry's computed once -/

/-- The codes of the registry's symbol names. -/
def Faithful.regSymCodesCD : List Nat := codes_of% regSymNames

/-- The codes of the registry's sort names. -/
def Faithful.regSortCodesCD : List Nat := codes_of% regSortNames

theorem Faithful.regSymCodesCD_eq : regSymNames.map strCode = regSymCodesCD := by decide +kernel

theorem Faithful.regSortCodesCD_eq : regSortNames.map strCode = regSortCodesCD := by decide +kernel

/-- The codes of the numbered symbols' names: the registry's, then the definition's own. -/
def Faithful.symCodesCD (c : Semantics) : List Nat := regSymCodesCD ++ c.symNames.map strCode

/-- The codes of the numbered sorts' names: the registry's, then the definition's own. -/
def Faithful.sortCodesCD (c : Semantics) : List Nat := regSortCodesCD ++ c.sortNames.map strCode

theorem Faithful.symCodesCD_eq (c : Semantics) : (allSymNames c).map strCode = symCodesCD c := by
  rw [allSymNames, List.map_append, regSymCodesCD_eq, symCodesCD]

theorem Faithful.sortCodesCD_eq (c : Semantics) : (allSortNames c).map strCode = sortCodesCD c := by
  rw [allSortNames, List.map_append, regSortCodesCD_eq, sortCodesCD]

/-- `namesNumbered`, decided on the names' codes. -/
theorem Faithful.namesNumbered_of_codesCD (h : namesNumberedC c (iteIdx (symCodesCD c)) = true) :
    namesNumbered c = true :=
  namesNumbered_of_codes (symCodesCD_eq c) rfl h

/-- `namesApartK`, decided on the names' codes. -/
theorem Faithful.namesApartK_of_codesCD (h : namesApartC c (symCodesCD c) (sortCodesCD c) = true) :
    namesApartK c = true :=
  namesApartK_of_codes (symCodesCD_eq c) (sortCodesCD_eq c) h

/-- `itesApart`, decided on the names' codes. -/
theorem Faithful.itesApart_of_codesCD
    (h : itesApartC c (iteIdx (symCodesCD c)) (sortCodesCD c) = true) : itesApart c = true :=
  itesApart_of_codes (symCodesCD_eq c) (sortCodesCD_eq c) rfl h

/-- No symbol is named like `ite` at a sort when no name's code is one of such a name
(`iteIdx` empty). -/
theorem Faithful.iteSort_none_of_iteIdxCD (h : iteIdx (symCodesCD c) = []) (f : Sym) :
    iteSort? (c.symName f) = none := by
  cases hs : iteSort? (c.symName f) with
  | none => rfl
  | some X =>
    have := mem_iteIdx (symCodesCD_eq c) (f := f) (by rw [hs]; exact Option.some_ne_none X)
    rw [h] at this
    exact absurd this List.not_mem_nil

/-- `sortedOK` from its conjuncts. -/
theorem Semantics.sortedOK_of_conjCD (h1 : c.subsortsOK = true)
    (h2 : c.fns.all (fun f => f.clauses.all (c.clauseSorted f (c.fns.map Fn.sig))) = true)
    (h3 : c.rules.all c.ruleSorted = true) (h4 : c.rulesPlain = true) (h5 : c.clausesPlain = true)
    (h6 : c.paramsPlain = true) : c.sortedOK = true := by
  simp only [Semantics.sortedOK, h1, h2, h3, h4, h5, h6, Bool.and_self]

/-- `coreOK` from the conjuncts of its conjuncts: those of `sortedOK`, those of `faithCoreOK`, and
the other four. -/
theorem Semantics.coreOK_of_partsCD (s1 : c.subsortsOK = true)
    (s2 : c.fns.all (fun f => f.clauses.all (c.clauseSorted f (c.fns.map Fn.sig))) = true)
    (s3 : c.rules.all c.ruleSorted = true) (s4 : c.rulesPlain = true) (s5 : c.clausesPlain = true)
    (s6 : c.paramsPlain = true)
    (h1 : namesNumbered c = true) (h2 : genWf c = true) (h3 : collSortsOK c = true)
    (h4 : collsOK c = true) (h5 : patHeadsOK c = true) (h6 : namesApartK c = true)
    (h7 : LitsApart c = true) (h8 : sortsNumbered c = true) (h10 : itesApart c = true)
    (h11 : kindsApart c = true) (h12 : ctorsOnce c = true) (h13 : fnsApart c = true)
    (hh : c.hooksApart = true) (hp : c.predsApart = true) (hi : c.idsOK = true)
    (ho : c.overloadsOK = true) : c.coreOK = true := by
  simp only [Semantics.coreOK, Semantics.sortedOK_of_conjCD s1 s2 s3 s4 s5 s6,
    Semantics.faithCoreOK_of_partsK h1 h2 h3 h4 h5 h6 h7 h8 h10 h11 h12 h13, hh, hp, hi, ho, Bool.and_self]

/-- `wf` from the conjuncts of its conjuncts: those of `namesOK`, of `okAll` and of `faithOK`, and
the other four. -/
theorem wf_of_partsCD {d : Definition}
    (n1 : KoreAML.nodup (d.emit.sortDecls.map (·.name)) = true)
    (n2 : KoreAML.nodup (d.emit.symbolDecls.map (·.name) ++ d.emit.aliasNames) = true)
    (n3 : d.sem.hooksApart = true) (n4 : d.sem.predsApart = true) (n5 : d.sem.idsOK = true)
    (o1 : d.sem.declsOK = true) (o2 : d.sem.rulesPlain = true) (o3 : d.sem.clausesPlain = true)
    (o4 : d.sem.paramsPlain = true) (o5 : d.sem.subsortsOK = true) (o6 : d.sem.fnsOKAll = true)
    (o7 : d.sem.rules.all d.sem.ruleOKAll = true) (o8 : d.sem.rules.all d.sem.rulePredsOK = true)
    (hc : d.cert.ok d.sem = true) (hp : d.pres.ok d.sem = true) (hpa : d.paramsOK = true)
    (f1 : namesNumbered d.sem = true) (f2 : genWf d.sem = true) (f3 : collSortsOK d.sem = true)
    (f4 : collsOK d.sem = true) (f5 : patHeadsOK d.sem = true) (f6 : namesApartK d.sem = true)
    (f7 : LitsApart d.sem = true) (f8 : sortsNumbered d.sem = true) (f9 : collsNotCtors d.sem = true)
    (f10 : itesApart d.sem = true) (f11 : kindsApart d.sem = true) (f12 : ctorsOnce d.sem = true)
    (f13 : fnsApart d.sem = true) (ho : d.sem.overloadsOK = true) : wf d = true := by
  simp only [wf, Definition.namesOK, Semantics.okAll, Semantics.faithOK, n1, n2, n3, n4, n5, o1, o2, o3,
    o4, o5, o6, o7, o8, hc, hp, hpa, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, ho,
    Bool.and_self]

/-- A Boolean conjunction from its two sides. -/
theorem and_true_of_CD {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  simp only [ha, hb, Bool.and_self]

/-- Two mapped lists agree when their first `n` entries and the rest agree. A kernel decision of a
block (`(l.drop i).take n`) reduces the list only as far as the block. -/
theorem map_eq_of_splitCD {α β : Type} {f g : α → β} {l l' : List α} (n : Nat)
    (h1 : (l.take n).map f = (l'.take n).map g) (h2 : (l.drop n).map f = (l'.drop n).map g) :
    l.map f = l'.map g := by
  rw [← List.take_append_drop n l, ← List.take_append_drop n l', List.map_append, List.map_append, h1, h2]

end KCore

/-- Closes `namesNumbered c = true` by a kernel decision on the names' codes. -/
macro "decide_namesNumbered" : tactic =>
  `(tactic| (refine KCore.Faithful.namesNumbered_of_codesCD ?_; decide +kernel))

/-- Closes `namesApartK c = true` by a kernel decision on the names' codes, or else of
`namesApartFast`. -/
macro "decide_namesApartK" : tactic =>
  `(tactic| first | (refine KCore.Faithful.namesApartK_of_codesCD ?_; decide +kernel) | (refine KCore.Faithful.Model.namesApartK_of_fast ?_; decide +kernel))

/-- Closes `itesApart c = true` by a kernel decision on the names' codes. -/
macro "decide_itesApart" : tactic =>
  `(tactic| (refine KCore.Faithful.itesApart_of_codesCD ?_; decide +kernel))

open Lean Elab Tactic in
/-- The constant at the head of the left side of a goal `b = true`, read off the goal's syntax
tree, without unfolding. -/
def KCore.boolGoalHeadCD : TacticM (Option Name) := do
  let t ← instantiateMVars (← getMainTarget)
  return match t.eq? with
    | some (_, lhs, rhs) => if rhs.isConstOf ``Bool.true then lhs.getAppFn.constName? else none
    | none => none

open Lean Elab Tactic in
/-- Closes `namesNumbered c = true`, `namesApartK c = true` or `itesApart c = true` on codes, any
other goal by `decide +kernel`; with the heartbeat budget of a declaration of its own, as each
conjunct is decided apart. -/
elab "decide_leafCD" : tactic => withCurrHeartbeats do
  match ← KCore.boolGoalHeadCD with
  | some ``KCore.Faithful.namesNumbered => evalTactic (← `(tactic| decide_namesNumbered))
  | some ``KCore.Faithful.Model.namesApartK => evalTactic (← `(tactic| decide_namesApartK))
  | some ``KCore.Faithful.Model.itesApart => evalTactic (← `(tactic| decide_itesApart))
  | _ => evalTactic (← `(tactic| decide +kernel))

/-- Closes `c.sortedOK = true`, each conjunct by a kernel decision of its own. -/
macro "decide_sortedOK" : tactic =>
  `(tactic| (refine KCore.Semantics.sortedOK_of_conjCD ?_ ?_ ?_ ?_ ?_ ?_ <;> decide_leafCD))

/-- Closes `c.faithCoreOK = true`, each conjunct by a decision of its own (`decide_leafCD`). -/
macro "decide_faithCoreOK" : tactic =>
  `(tactic| (refine KCore.Semantics.faithCoreOK_of_partsK ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> decide_leafCD))

/-- Closes `c.coreOK = true`, each conjunct of its conjuncts by a decision of its own
(`decide_leafCD`). -/
macro "decide_coreOK" : tactic =>
  `(tactic| (refine KCore.Semantics.coreOK_of_partsCD ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> decide_leafCD))

/-- Closes `wf d = true`, each conjunct of its conjuncts by a decision of its own (`decide_leafCD`). -/
macro "decide_wf" : tactic =>
  `(tactic| (refine KCore.wf_of_partsCD ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> decide_leafCD))

/-- Closes a conjunction, and a Boolean conjunction `(a && b) = true`, conjunct by conjunct, and a
goal `b = true` by the decider of its head:
`decide_coreOK`, `decide_faithCoreOK`, `decide_sortedOK`, `decide_wf`, or `decide_leafCD`, which
decides any other goal by `decide +kernel`. -/
syntax "decide_cheap" : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| decide_cheap) => do
    if (← instantiateMVars (← getMainTarget)).isAppOfArity ``And 2 then
      evalTactic (← `(tactic| (refine ⟨?_, ?_⟩ <;> decide_cheap)))
      return
    match ← KCore.boolGoalHeadCD with
    | some ``and => evalTactic (← `(tactic| (refine KCore.and_true_of_CD ?_ ?_ <;> decide_cheap)))
    | some ``KCore.Semantics.coreOK => evalTactic (← `(tactic| decide_coreOK))
    | some ``KCore.Semantics.faithCoreOK => evalTactic (← `(tactic| decide_faithCoreOK))
    | some ``KCore.Semantics.sortedOK => evalTactic (← `(tactic| decide_sortedOK))
    | some ``KCore.wf => evalTactic (← `(tactic| decide_wf))
    | _ => evalTactic (← `(tactic| decide_leafCD))

/-- `decide_map_blocks n k` closes `l.map f = l'.map g` by `k` blocks of `n` entries and the rest,
each a kernel decision of its own (`map_eq_of_splitCD`). -/
syntax "decide_map_blocks " num num : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| decide_map_blocks $n $k) => do
    for _ in [0:k.getNat] do
      evalTactic (← `(tactic| refine KCore.map_eq_of_splitCD $n ?_ ?_))
      withCurrHeartbeats <| evalTactic (← `(tactic| focus decide +kernel))
    withCurrHeartbeats <| evalTactic (← `(tactic| decide +kernel))
