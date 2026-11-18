/-
  KCore. A variable held by a cut, at a value.

  `memHeldH c H bound pre i`: a conjunct `V ∈ t` of `pre` has V among `bound` and t holding the
  variable i under constructors, injections and the symbols H names (`occsUnder c H`). The landed
  `memHeld` is it at `Semantics.holds` (`memHeld_eq_H`).

  - `memHeldH_witnessedAt`: in a model of `Γ`, at a valuation of the variables in their sorts that
    gives each variable of `bound` the element of a value, where `pre` holds at some element and
    each cut of `pre` is well sorted, the valuation gives a `memHeldH` variable the element of a
    value of its sort, for every H whose symbols have `HeldBack`. The bound variable's value is in
    the cut's term (`mem_elem`), and `occsUnder_witnessed` at that term gives the rest.
  - `memHeld_valuesB`: the same at a well-sorted rule, in a model of `Γc`, with `bound` the left
    side's variables: the left side holding at a value's element makes them values' elements.
  - `memHeldH_not_closed`: a rule one of whose variables is `memHeldH` over its left side's
    variables has `reqClosed` false, so `needsWitness` false.
-/
import KcoreSpec.HeldValues

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace KCore

open ML Faithful
open KoreAML (DefOK Inh IsSort Closed VarKey VarTable)

/-- The variable i is held by a cut, over a set H of held symbols: a conjunct `V ∈ t`, V among
`bound`, t holding i under constructors, injections and the symbols H names. -/
def memHeldH (c : Semantics) (H : Sym → Bool) (bound : List Nat) (pre : Cond) (i : Nat) : Bool :=
  pre.conjuncts.any fun
    | .mem _ (.var v) t => bound.contains v && (occsUnder c H t).contains i
    | _ => false

/-- What holds of a condition and passes to both sides of every `and` holds of each conjunct. -/
theorem conjuncts_spec (P : Cond → Prop) (hand : ∀ p q, P (.and p q) → P p ∧ P q) :
    ∀ p, P p → ∀ q ∈ p.conjuncts, P q := by
  intro p
  induction p with
  | and a b iha ihb =>
    intro hp q hq
    rw [Cond.conjuncts] at hq
    rcases List.mem_append.mp hq with h | h
    · exact iha (hand a b hp).1 q h
    · exact ihb (hand a b hp).2 q h
  | _ =>
    intro hp q hq
    simp only [Cond.conjuncts, List.mem_singleton] at hq
    subst hq; exact hp

/-- The cut that holds a `memHeldH` variable. -/
theorem memHeldH_parts {c : Semantics} {H : Sym → Bool} {bound : List Nat} {pre : Cond} {i : Nat}
    (h : memHeldH c H bound pre i = true) :
    ∃ s v t, Cond.mem s (.var v) t ∈ pre.conjuncts ∧ v ∈ bound ∧ i ∈ occsUnder c H t := by
  simp only [memHeldH, List.any_eq_true] at h
  obtain ⟨q, hq, hqi⟩ := h
  split at hqi
  · rename_i s v t
    simp only [Bool.and_eq_true] at hqi
    exact ⟨s, v, t, hq, List.contains_iff_mem.mp hqi.1, List.contains_iff_mem.mp hqi.2⟩
  · cases hqi

/-- A cut of `pre` with its variable in `bound` and its term holding i makes i `memHeldH`. -/
theorem memHeldH_of_parts {c : Semantics} {H : Sym → Bool} {bound : List Nat} {pre : Cond} {i : Nat}
    {s : Srt} {v : Nat} {t : Term} (hq : Cond.mem s (.var v) t ∈ pre.conjuncts) (hv : v ∈ bound)
    (hi : i ∈ occsUnder c H t) : memHeldH c H bound pre i = true := by
  simp only [memHeldH, List.any_eq_true]
  exact ⟨_, hq, by simp only [Bool.and_eq_true]; exact ⟨List.contains_iff_mem.mpr hv, List.contains_iff_mem.mpr hi⟩⟩

/-- The landed `memHeld` is `memHeldH` at `Semantics.holds`. -/
theorem memHeld_eq_H (c : Semantics) (bound : List Nat) (pre : Cond) (i : Nat) :
    memHeld c bound pre i = memHeldH c c.holds bound pre i := by
  simp only [memHeld, memHeldH, heldOccs_eq]
  rfl

mutual
  /-- The variables a term holds under a set of symbols are among its variables. -/
  theorem occsUnder_varOccs (c : Semantics) (H : Sym → Bool) : ∀ (t : Term), ∀ i ∈ occsUnder c H t, i ∈ varOccs t
    | .var j, i, hi => by rw [occsUnder] at hi; rw [varOccs]; exact hi
    | .app f ts, i, hi => by
      rw [occsUnder] at hi
      rw [varOccs]
      split at hi
      · exact occsUnderList_varOccs c H ts i hi
      · cases hi
    | .inj _ _ t, i, hi => by
      rw [occsUnder] at hi
      rw [varOccs]
      exact occsUnder_varOccs c H t i hi
    | .as t j, i, hi => by
      rw [occsUnder] at hi
      rw [varOccs]
      rcases List.mem_append.mp hi with hi | hi
      · exact List.mem_append_left _ (occsUnder_varOccs c H t i hi)
      · exact List.mem_append_right _ hi
    | .dv _ _, i, hi => by rw [occsUnder] at hi; cases hi
  theorem occsUnderList_varOccs (c : Semantics) (H : Sym → Bool) :
      ∀ (ts : List Term), ∀ i ∈ occsUnderList c H ts, i ∈ varOccsList ts
    | [], i, hi => by rw [occsUnderList] at hi; cases hi
    | t :: ts, i, hi => by
      rw [occsUnderList] at hi
      rw [varOccsList]
      rcases List.mem_append.mp hi with hi | hi
      · exact List.mem_append_left _ (occsUnder_varOccs c H t i hi)
      · exact List.mem_append_right _ (occsUnderList_varOccs c H ts i hi)
end

/-- A conjunct's variables are among the condition's. -/
theorem conjuncts_varOccs (n : Nat) (pre : Cond) :
    ∀ q ∈ pre.conjuncts, ∀ j ∈ varOccsCond n q, j ∈ varOccsCond n pre :=
  conjuncts_spec (fun q => ∀ j ∈ varOccsCond n q, j ∈ varOccsCond n pre)
    (fun a b hp => ⟨fun j hj => hp j (by rw [varOccsCond]; exact List.mem_append_left _ hj),
      fun j hj => hp j (by rw [varOccsCond]; exact List.mem_append_right _ hj)⟩) pre (fun j hj => hj)

/-- A `memHeldH` variable is a variable of the condition, held by a cut whose variable is in
`bound` and a variable of the condition, and whose term's variables are the condition's. -/
theorem memHeldH_condVar {c : Semantics} {H : Sym → Bool} {bound : List Nat} {pre : Cond} {i : Nat} (n : Nat)
    (h : memHeldH c H bound pre i = true) :
    (∃ v ∈ bound, v ∈ varOccsCond n pre) ∧ i ∈ varOccsCond n pre := by
  obtain ⟨s, v, t, hq, hv, hi⟩ := memHeldH_parts h
  have hsub := conjuncts_varOccs n pre _ hq
  exact ⟨⟨v, hv, hsub v (by rw [varOccsCond, varOccs]; exact List.mem_append_left _ (List.mem_singleton.mpr rfl))⟩,
    hsub i (by rw [varOccsCond]; exact List.mem_append_right _ (occsUnder_varOccs c H t i hi))⟩

/-- A condition with a `memHeldH` variable is not `\top`. -/
theorem memHeldH_not_top {c : Semantics} {H : Sym → Bool} {bound : List Nat} {pre : Cond} {i : Nat}
    (h : memHeldH c H bound pre i = true) : pre.isTop = false := by
  cases pre with
  | top => simp [memHeldH, Cond.conjuncts] at h
  | _ => rfl

/-- **A rule with a cut that holds a variable has `reqClosed` false and `needsWitness` false**:
the cut's variable is a condition variable the left side binds. -/
theorem memHeldH_not_closed {c : Semantics} {H : Sym → Bool} {r : Rule} {i : Nat}
    (h : memHeldH c H (varOccs r.lhs) r.pre i = true) : r.reqClosed = false ∧ r.needsWitness c = false := by
  obtain ⟨⟨v, hv, hvc⟩, -⟩ := memHeldH_condVar r.vars.length h
  have hcl : r.reqClosed = false := by
    cases hc : r.reqClosed with
    | false => rfl
    | true =>
      unfold Rule.reqClosed at hc
      have := List.all_eq_true.mp hc v (by unfold Rule.condVars; exact List.mem_append_right _ hvc)
      rw [List.contains_iff_mem.mpr hv] at this
      simp at this
  exact ⟨hcl, by unfold Rule.needsWitness; rw [hcl]; simp⟩

/-- `memHeldH_not_closed` at the landed `memHeld`. -/
theorem memHeld_not_closed {c : Semantics} {r : Rule} {i : Nat}
    (h : memHeld c (varOccs r.lhs) r.pre i = true) : r.reqClosed = false ∧ r.needsWitness c = false :=
  memHeldH_not_closed (by rw [← memHeld_eq_H]; exact h)

/-- A cut of a well-sorted condition: its variable and its term have the sort it names, a numbered
sort. -/
theorem conjuncts_memOK {c : Semantics} {vars : List Srt} {pre : Cond} (hok : c.condOK vars pre = true)
    {s : Srt} {v : Nat} {t : Term} (hq : Cond.mem s (.var v) t ∈ pre.conjuncts) :
    vars[v]? = some s ∧ sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t = some s ∧
      s < nRegSorts + c.sortNames.length := by
  have hqok := conjuncts_spec (fun q => c.condOK vars q = true)
    (fun a b hp => by rw [Semantics.condOK, Bool.and_eq_true] at hp; exact hp) pre hok _ hq
  simp only [Semantics.condOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hqok
  exact ⟨sortOfTerm_var.mp hqok.1.1, hqok.1.2, hqok.2⟩

section At
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M} (hI : I ⊧ᴵP Γ c)
  [OvlOK c] (hg : genWf c = true)
  (htr : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts)
  (hnm : NamesPlain c) {vars : List Srt} {vs : List KoreAML.Var} {tbl : VarTable} {e : Valuation M}
  (hvs : vs.length = vars.length)
  (hin : ∀ i < vars.length, InS I (c.sortName (vars.getD i 0)) (e.evalEvar (tbl.ev (keyAt vs i))))
  {L : List CtorSig} (hL : HeadsOK c L) {H : Sym → Bool}
  (hback : ∀ f k, c.isCtor f = false → H f = true → lookupSig (c.rhsCtx L).heads f = some k → HeldBack c I f k)
include hI hg htr hnm hvs hin hL hback

/-- **A variable held by a cut, at a value** (over a list of sorts and a set H of symbols). At a
valuation of the variables in their sorts that gives each variable of `bound` the element of a
value, where `pre` holds at some element and each cut `V ∈ t` of `pre` has V and t at the sort it
names, a numbered one: the valuation gives each `memHeldH` variable the element of a value of its
sort. -/
theorem memHeldH_witnessedAt {bound : List Nat} (hbound : ∀ v ∈ bound, Witnessed c I tbl vs vars e v)
    {pre : Cond}
    (hok : ∀ s v t, Cond.mem s (.var v) t ∈ pre.conjuncts → vars[v]? = some s ∧
      sortOfTerm (c.rhsCtx L) vars t = some s ∧ s < nRegSorts + c.sortNames.length)
    {S : Srt} (hS : S < nRegSorts + c.sortNames.length) {a : M}
    (hpre : (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c vs (srtOf c S) pre)).interpret I e a)
    (i : Nat) (hi : memHeldH c H bound pre i = true) : Witnessed c I tbl vs vars e i := by
  obtain ⟨s, v, t, hq, hvb, hti⟩ := memHeldH_parts hi
  obtain ⟨hvs', hts, hsn⟩ := hok s v t hq
  have hqm := conjuncts_spec (fun q => (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c vs (srtOf c S) q)).interpret I e a)
    (fun p q hp => by rw [Cond.kore, tr_and2, KoreAML.interp_sAnd] at hp; exact hp) pre hpre _ hq
  obtain ⟨w, hw, hwe⟩ := hbound v hvb
  rw [List.getD_eq_getElem?_getD, hvs', Option.getD_some] at hw
  have hinv := hin v (List.getElem?_eq_some_iff.mp hvs').1
  rw [List.getD_eq_getElem?_getD, hvs', Option.getD_some] at hinv
  have hmt := mem_elem hI hsn hS hinv hqm
  rw [← hwe] at hmt
  exact occsUnder_witnessed hI hg htr hnm hvs hin hL hback hts hw hmt i hti

end At

section Rule
variable {c : Semantics} {M : Type} [Inhabited M] {I : Interpretation KoreAML.Sym M}

/-- **A variable held by a cut of a rule, at a value**: in a model of `Γc`, a valuation of a
well-sorted rule's variables in their sorts under which the left side holds at a value's element
and `pre` holds there gives every variable that is `memHeldH` over the left side's variables the
element of a value of its sort, for every H whose symbols that are no constructor have `HeldBack`
in the model. -/
theorem memHeld_valuesB (h : c.coreOK = true) (hI : I ⊧ᴵP Γc c) {H : Sym → Bool}
    (hback : ∀ f k, c.isCtor f = false → H f = true →
      lookupSig (c.rhsCtx (c.fns.map Fn.sig)).heads f = some k → HeldBack c I f k)
    {r : Rule} (hs : c.ruleSorted r = true) {tbl : VarTable} {e : Valuation M}
    (hin : ∀ i < r.vars.length, InS I (c.sortName (r.vars.getD i 0))
      (e.evalEvar (tbl.ev (keyAt (canonVars c r.vars) i))))
    (x : Config c)
    (hl : (KoreAML.tr ⟨tbl, []⟩ (Term.kore c (canonVars c r.vars) r.lhs)).interpret I e (elemOf c I x.val))
    (hpre : (KoreAML.tr ⟨tbl, []⟩ (Cond.kore c (canonVars c r.vars) (srtOf c topCellSort) r.pre)).interpret I e
      (elemOf c I x.val))
    (i : Nat) (hi : memHeldH c H (varOccs r.lhs) r.pre i = true) :
    Witnessed c I tbl (canonVars c r.vars) r.vars e i := by
  obtain ⟨hok, hsr, hnn, hg, hph, hcso, hcs, hph', hno⟩ := hypSound_of_core h
  haveI : OvlOK c := hno
  have hsc := sortCtx_of_all hok hsr (OvlOK.ovlCase hno)
  have hIΓ : I ⊧ᴵP Γ c := fun φ hφ => hI φ (Or.inl hφ)
  obtain ⟨hlhs, -, -, -⟩ := Semantics.ruleSorted_parts c hs
  obtain ⟨-, hwitL⟩ := patVal_backC hIΓ hph hcs hcso hg hsc.trans hnn.1 (canonVars_length c r.vars) hin
    (collPat_of_sorted hph' hlhs) (OvlOK.nf_bridge inferInstance hlhs) x.property hl
  have hokP : c.condOK r.vars r.pre = true := by
    simp only [Semantics.ruleSorted, Bool.and_eq_true] at hs
    exact hs.1.1.1.1.1.2
  exact memHeldH_witnessedAt hIΓ hg hsc.trans hnn.1 (canonVars_length c r.vars) hin fns_headsOK hback hwitL
    (fun s v t hq => conjuncts_memOK hokP hq) top_numbered hpre i hi

end Rule

end KCore
