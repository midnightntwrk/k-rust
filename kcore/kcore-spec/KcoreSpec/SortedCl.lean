/-
  KCore. A clause whose patterns need not bind every variable, asked CN-4's bodies as decided
  conditions of their own:
  - `Semantics.clauseSortedOpen`: `clauseSorted` with "each variable occurs in the clause" (its
    patterns, conditions, right side, `ensures` or right side's predicate) in place of "the patterns
    bind each variable";
  - `Semantics.clausePlainOpen`: what `clausesPlain` asks of one clause, with the conjunct on open
    condition variables: none, or closed conditions, or each of a confined sort;
  - `Semantics.sortedOKCl`: `sortedOK` with each clause asked these two; `sortedOK` gives it
    (`Semantics.sortedOKCl_of_sortedOK`).
-/
import KcoreSpec.Obligations
import KcoreSpec.FaithOK
import KcoreSpec.SubjectReduction

set_option autoImplicit false

namespace KCore

/-- `clauseSorted` with "each of its variables occurs in it" in place of "its patterns bind each of
its variables": its patterns have the argument sorts in a left-hand side's context, each variable
occurs in its patterns, its conditions, its right-hand side, its `ensures` or its right side's
predicate, its `requires` is a Bool, its right-hand side has the result sort, its `ensures` is a
Bool, each binder of its predicates ranges where values and elements agree, and its premise's
predicate is well sorted. -/
def Semantics.clauseSortedOpen (c : Semantics) (f : Fn) (rhsHeads : List CtorSig) (cl : Clause) : Bool :=
  sortsOfTerms c.patCtxAll cl.vars cl.pats == some f.args &&
  binds cl.vars.length (varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
    (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post) &&
  reqOK (c.rhsCtx rhsHeads) cl.vars cl.req &&
  sortOfTerm (c.rhsCtx rhsHeads) cl.vars cl.rhs == some f.result &&
  reqOK (c.rhsCtx rhsHeads) cl.vars cl.ens &&
  (Cond.bound c cl.vars.length cl.pre && Cond.bound c cl.vars.length cl.post) &&
  c.condOK cl.vars cl.pre

/-- What `clausesPlain` asks of one clause, with the conjunct on its open condition variables: no
variable bound by `\exists`, a `\top` predicate on the right side, a `\top` predicate in the premise
or conditions that need no witness, and no open condition variable, or closed conditions, or each
open condition variable of a confined sort. -/
def Semantics.clausePlainOpen (c : Semantics) (cl : Clause) : Bool :=
  cl.exs.isEmpty && (cl.pre.isTop || !cl.needsWitness c) && cl.post.isTop &&
  (!cl.reqOpen || cl.reqClosed || cl.openCondVars.all fun i => (cl.vars[i]?.map c.confined).getD false)

theorem Semantics.clauseSortedOpen_parts {c : Semantics} {f : Fn} {H : List CtorSig} {cl : Clause}
    (h : c.clauseSortedOpen f H cl = true) :
    sortsOfTerms c.patCtxAll cl.vars cl.pats = some f.args ∧
      (∀ i < cl.vars.length, i ∈ varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
        (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post) ∧
      (∀ t, cl.req = some t → sortOfTerm (c.rhsCtx H) cl.vars t = some Srt.bool) ∧
      sortOfTerm (c.rhsCtx H) cl.vars cl.rhs = some f.result ∧
      (∀ t, cl.ens = some t → sortOfTerm (c.rhsCtx H) cl.vars t = some Srt.bool) := by
  simp only [Semantics.clauseSortedOpen, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hpats, hb⟩, hreq⟩, hrhs⟩, hens⟩, -⟩, -⟩ := h
  refine ⟨hpats, fun i hi => ?_, fun t ht => ?_, hrhs, fun t ht => ?_⟩
  · simp only [binds, List.all_eq_true, List.mem_range, List.contains_iff_mem] at hb
    exact hb i hi
  · rw [ht] at hreq; simpa [reqOK] using hreq
  · rw [ht] at hens; simpa [reqOK] using hens

/-- What `clausePlainOpen` gives of a clause: no existential variable, the right side's predicate
`\top`, the conjunct on its open condition variables, and where its premise's predicate is not
`\top`, conditions that need no witness (`needsWitness`). -/
theorem Semantics.clausePlainOpen_partsP {c : Semantics} {cl : Clause} (h : c.clausePlainOpen cl = true) :
    cl.exs = [] ∧ cl.post = .top ∧
      (!cl.reqOpen || cl.reqClosed || cl.openCondVars.all fun i => (cl.vars[i]?.map c.confined).getD false) = true ∧
      (cl.pre ≠ .top → cl.needsWitness c = false) := by
  simp only [Semantics.clausePlainOpen, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hex, hpre⟩, hpost⟩, hrest⟩ := h
  refine ⟨List.isEmpty_iff.mp hex, Cond.eq_top_of_isTop hpost, hrest, fun hne => ?_⟩
  rcases Bool.or_eq_true_iff.mp hpre with ht | hn
  · exact absurd (Cond.eq_top_of_isTop ht) hne
  · simpa using hn

/-- A clause with `clauseSortedOpen` has a well-sorted predicate in its premise. -/
theorem Semantics.clauseSortedOpen_preOK {c : Semantics} {f : Fn} {H : List CtorSig} {cl : Clause}
    (h : c.clauseSortedOpen f H cl = true) : c.condOK cl.vars cl.pre = true := by
  simp only [Semantics.clauseSortedOpen, Bool.and_eq_true] at h
  exact h.2

/-- `clauseSorted` asks what `clauseSortedOpen` asks. -/
theorem Semantics.clauseSortedOpen_of_sorted {c : Semantics} {f : Fn} {H : List CtorSig} {cl : Clause}
    (h : c.clauseSorted f H cl = true) : c.clauseSortedOpen f H cl = true := h

/-- The variables of a clause's `requires` are among its conditions'. -/
theorem Clause.req_condVars {cl : Clause} {t : Term} (ht : cl.req = some t) : ∀ i ∈ varOccs t, i ∈ cl.condVars :=
  fun i hi => List.mem_append_left _ (by rw [ht]; exact hi)

/-- The variables of a clause's `requires` are among those of its patterns and conditions. -/
theorem Clause.req_leftVars {cl : Clause} {t : Term} (ht : cl.req = some t) : ∀ i ∈ varOccs t, i ∈ cl.leftVars :=
  fun i hi => List.mem_append_right _ (Clause.req_condVars ht i hi)

/-- The conditions of a clause with a `\top` premise predicate are its `requires`. -/
theorem Clause.condVars_of_top {cl : Clause} (hpre : cl.pre = .top) :
    cl.condVars = (cl.req.map varOccs).getD [] := by
  simp [Clause.condVars, hpre, varOccsCond]


/-- `sortedOK` with each clause asked `clauseSortedOpen` and `clausePlainOpen`: the sorts and
subsorts, each clause well sorted with each of its variables occurring in it, its predicates `\top`,
no variable bound by `\exists`, and its open condition variables of confined sorts or its
conditions closed; the rules well sorted and plain; the parameters plain. -/
def Semantics.sortedOKCl (c : Semantics) : Bool :=
  c.subsortsOK && c.fns.all (fun f => f.clauses.all fun cl =>
      c.clauseSortedOpen f (c.fns.map Fn.sig) cl && c.clausePlainOpen cl) &&
    c.rules.all c.ruleSorted && c.rulesPlain && c.paramsPlain

theorem Semantics.sortedOKCl_parts {c : Semantics} (h : c.sortedOKCl = true) :
    c.subsortsOK = true ∧
      (∀ f ∈ c.fns, ∀ cl ∈ f.clauses, c.clauseSortedOpen f (c.fns.map Fn.sig) cl = true ∧ c.clausePlainOpen cl = true) ∧
      c.rules.all c.ruleSorted = true ∧ c.rulesPlain = true ∧ c.paramsPlain = true := by
  simp only [Semantics.sortedOKCl, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, fun f hf cl hcl => ?_, h3, h4, h5⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp h2 f hf) cl hcl
  simpa only [Bool.and_eq_true] using this

/-- What `sortedOKCl` asks of an open generator (`paramsPlain`'s raw branch). -/
theorem Semantics.raw_of_sortedOKCl {c : Semantics} (h : c.sortedOKCl = true) {k : ParamSig}
    (hk : k ∈ c.params) (hr : k.raw = true) :
    k.impl = none ∧
    ((k.assoc || k.idem) = true → k.sig.args = [k.sig.result, k.sig.result]) ∧
    nRegSyms ≤ k.sig.name ∧ iteSort? (c.symName k.sig.name) = none ∧
    c.shapesOK = true :=
  Semantics.raw_of_paramsPlain (Semantics.sortedOKCl_parts h).2.2.2.2 hk hr

/-- **`sortedOK` gives `sortedOKCl`**: the two ask the same of each clause (`clauseSorted` is
`clauseSortedOpen`, and `clausesPlain` asks `clausePlainOpen` of each clause). -/
theorem Semantics.sortedOKCl_of_sortedOK {c : Semantics} (h : c.sortedOK = true) : c.sortedOKCl = true := by
  have hs := Semantics.sortedOK_sorted h
  have hp : c.clausesPlain = true := by
    simp only [Semantics.sortedOK, Bool.and_eq_true] at h; exact h.1.2
  have hcl : ∀ f ∈ c.fns, ∀ cl ∈ f.clauses, (c.clauseSortedOpen f (c.fns.map Fn.sig) cl && c.clausePlainOpen cl) = true := by
    intro f hf cl hcl
    have hcs : c.clauseSorted f (c.fns.map Fn.sig) cl = true := by
      simp only [Bool.and_eq_true, List.all_eq_true] at hs
      exact hs.1.2 f hf cl hcl
    have hcp : c.clausePlainOpen cl = true := List.all_eq_true.mp (List.all_eq_true.mp hp f hf) cl hcl
    rw [Bool.and_eq_true]
    exact ⟨Semantics.clauseSortedOpen_of_sorted hcs, hcp⟩
  simp only [Semantics.sortedOK, Bool.and_eq_true] at h
  simp only [Semantics.sortedOKCl, Bool.and_eq_true]
  exact ⟨⟨⟨⟨h.1.1.1.1.1, List.all_eq_true.mpr fun f hf => List.all_eq_true.mpr (hcl f hf)⟩, h.1.1.1.2⟩, h.1.1.2⟩, h.2⟩

/-- A rule of a semantics `sortedOKCl` accepts whose left side binds every variable has no
existential variable (`Semantics.exs_nil_of_binds`). -/
theorem Semantics.sortedOKCl_exsNil {c : Semantics} (h : c.sortedOKCl = true) {r : Rule} (hr : r ∈ c.rules)
    (hb : binds r.vars.length (varOccs r.lhs) = true) : r.exs = [] := by
  obtain ⟨-, -, hrs, -, -⟩ := Semantics.sortedOKCl_parts h
  exact Semantics.exs_nil_of_binds (List.all_eq_true.mp hrs r hr) hb


/-! ## A clause with existential variables -/

/-- The existential variables of a clause are in scope, apart and in no pattern or condition of
the left side, and its right-side predicate is sorted. -/
def Semantics.clauseExOK (c : Semantics) (cl : Clause) : Bool :=
  cl.exs.all (· < cl.vars.length) && nodup cl.exs && cl.exs.all (fun i => !cl.leftVars.contains i) &&
    c.condOK cl.vars cl.post

/-- `clausePlainOpen` with "no variable bound by `\exists`, a `\top` predicate on the right side"
asked only together: a clause without existential variables has a `\top` predicate on its right
side, and a clause with existential variables has any. In both cases `clauseExOK`, a `\top`
predicate in the premise or conditions that need no witness, and the conjunct on the open condition
variables. -/
def Semantics.clausePlainOpenEx (c : Semantics) (cl : Clause) : Bool :=
  (!cl.exs.isEmpty || cl.post.isTop) && c.clauseExOK cl && (cl.pre.isTop || !cl.needsWitness c) &&
  (!cl.reqOpen || cl.reqClosed || cl.openCondVars.all fun i => (cl.vars[i]?.map c.confined).getD false)

/-- A clause without existential variables and with a `\top` predicate on its right side has
`clauseExOK`. -/
theorem Semantics.clauseExOK_of_plainSOE {c : Semantics} {cl : Clause} (hex : cl.exs = [])
    (hpost : cl.post = .top) : c.clauseExOK cl = true := by
  simp [Semantics.clauseExOK, hex, hpost, nodup, Semantics.condOK]

/-- **On a clause without existential variables `clausePlainOpenEx` is `clausePlainOpen`.** -/
theorem Semantics.clausePlainOpenEx_eq_of_noExs {c : Semantics} {cl : Clause} (hex : cl.exs = []) :
    c.clausePlainOpenEx cl = c.clausePlainOpen cl := by
  cases hp : cl.post.isTop
  · simp [Semantics.clausePlainOpenEx, Semantics.clausePlainOpen, hex, hp]
  · simp [Semantics.clausePlainOpenEx, Semantics.clausePlainOpen, hex, hp,
      Semantics.clauseExOK_of_plainSOE hex (Cond.eq_top_of_isTop hp)]

/-- `clausePlainOpen` gives `clausePlainOpenEx`. -/
theorem Semantics.clausePlainOpenEx_of_plainOpen {c : Semantics} {cl : Clause}
    (h : c.clausePlainOpen cl = true) : c.clausePlainOpenEx cl = true := by
  rw [Semantics.clausePlainOpenEx_eq_of_noExs (Semantics.clausePlainOpen_partsP h).1]; exact h

/-- What `clausePlainOpenEx` gives of a clause: `clauseExOK`, a `\top` predicate on the right side
where it has no existential variable, the conjunct on its open condition variables, and where its
premise's predicate is not `\top`, conditions that need no witness. -/
theorem Semantics.clausePlainOpenEx_parts {c : Semantics} {cl : Clause} (h : c.clausePlainOpenEx cl = true) :
    c.clauseExOK cl = true ∧ (cl.exs = [] → cl.post = .top) ∧
      (!cl.reqOpen || cl.reqClosed || cl.openCondVars.all fun i => (cl.vars[i]?.map c.confined).getD false) = true ∧
      (cl.pre ≠ .top → cl.needsWitness c = false) := by
  simp only [Semantics.clausePlainOpenEx, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hex, hok⟩, hpre⟩, hrest⟩ := h
  refine ⟨hok, fun he => ?_, hrest, fun hne => ?_⟩
  · rcases Bool.or_eq_true_iff.mp hex with hn | ht
    · simp [he] at hn
    · exact Cond.eq_top_of_isTop ht
  · rcases Bool.or_eq_true_iff.mp hpre with ht | hn
    · exact absurd (Cond.eq_top_of_isTop ht) hne
    · simpa using hn

/-- A clause with `clausePlainOpenEx` and no existential variable has `clausePlainOpen`. -/
theorem Semantics.clausePlainOpen_of_ex_noExs {c : Semantics} {cl : Clause}
    (h : c.clausePlainOpenEx cl = true) (hex : cl.exs = []) : c.clausePlainOpen cl = true := by
  rw [← Semantics.clausePlainOpenEx_eq_of_noExs hex]; exact h

/-- `sortedOKCl` with each clause asked `clausePlainOpenEx` for `clausePlainOpen`: a clause may bind
variables by `\exists` and then has any sorted predicate on its right side (`clauseExOK`). What the
value model reads of the clauses. -/
def Semantics.sortedOKClEx (c : Semantics) : Bool :=
  c.subsortsOK && c.fns.all (fun f => f.clauses.all fun cl =>
      c.clauseSortedOpen f (c.fns.map Fn.sig) cl && c.clausePlainOpenEx cl) &&
    c.rules.all c.ruleSorted && c.rulesPlain && c.paramsPlain

theorem Semantics.sortedOKClEx_parts {c : Semantics} (h : c.sortedOKClEx = true) :
    c.subsortsOK = true ∧
      (∀ f ∈ c.fns, ∀ cl ∈ f.clauses, c.clauseSortedOpen f (c.fns.map Fn.sig) cl = true ∧ c.clausePlainOpenEx cl = true) ∧
      c.rules.all c.ruleSorted = true ∧ c.rulesPlain = true ∧ c.paramsPlain = true := by
  simp only [Semantics.sortedOKClEx, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, fun f hf cl hcl => ?_, h3, h4, h5⟩
  have := List.all_eq_true.mp (List.all_eq_true.mp h2 f hf) cl hcl
  simpa only [Bool.and_eq_true] using this

/-- `sortedOKClEx` from its parts. -/
theorem Semantics.sortedOKClEx_of_parts {c : Semantics} (h1 : c.subsortsOK = true)
    (h2 : ∀ f ∈ c.fns, ∀ cl ∈ f.clauses, c.clauseSortedOpen f (c.fns.map Fn.sig) cl = true ∧ c.clausePlainOpenEx cl = true)
    (h3 : c.rules.all c.ruleSorted = true) (h4 : c.rulesPlain = true) (h5 : c.paramsPlain = true) :
    c.sortedOKClEx = true := by
  simp only [Semantics.sortedOKClEx, Bool.and_eq_true]
  refine ⟨⟨⟨⟨h1, List.all_eq_true.mpr fun f hf => List.all_eq_true.mpr fun cl hcl => ?_⟩, h3⟩, h4⟩, h5⟩
  rw [Bool.and_eq_true]; exact h2 f hf cl hcl

/-- **`sortedOKCl` gives `sortedOKClEx`.** -/
theorem Semantics.sortedOKClEx_of_sortedOKCl {c : Semantics} (h : c.sortedOKCl = true) : c.sortedOKClEx = true := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := Semantics.sortedOKCl_parts h
  exact Semantics.sortedOKClEx_of_parts h1
    (fun f hf cl hcl => ⟨(h2 f hf cl hcl).1, Semantics.clausePlainOpenEx_of_plainOpen (h2 f hf cl hcl).2⟩) h3 h4 h5

/-- **Where no clause has an existential variable, `sortedOKClEx` is `sortedOKCl`.** -/
theorem Semantics.sortedOKClEx_eq_of_noExs {c : Semantics}
    (hex : ∀ f ∈ c.fns, ∀ cl ∈ f.clauses, cl.exs = []) : c.sortedOKClEx = c.sortedOKCl := by
  have hfns : (c.fns.all fun f => f.clauses.all fun cl =>
        c.clauseSortedOpen f (c.fns.map Fn.sig) cl && c.clausePlainOpenEx cl) =
      (c.fns.all fun f => f.clauses.all fun cl =>
        c.clauseSortedOpen f (c.fns.map Fn.sig) cl && c.clausePlainOpen cl) := by
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true]
    constructor
    · intro h f hf cl hcl
      rw [← Semantics.clausePlainOpenEx_eq_of_noExs (hex f hf cl hcl)]; exact h f hf cl hcl
    · intro h f hf cl hcl
      rw [Semantics.clausePlainOpenEx_eq_of_noExs (hex f hf cl hcl)]; exact h f hf cl hcl
  simp only [Semantics.sortedOKClEx, Semantics.sortedOKCl, hfns]

/-- `sortedOKCl` from `sortedOKClEx` where no clause has an existential variable. -/
theorem Semantics.sortedOKCl_of_ex_noExs {c : Semantics} (h : c.sortedOKClEx = true)
    (hex : ∀ f ∈ c.fns, ∀ cl ∈ f.clauses, cl.exs = []) : c.sortedOKCl = true := by
  rw [← Semantics.sortedOKClEx_eq_of_noExs hex]; exact h

/-- `sortedOKCl` leaves no clause an existential variable. -/
theorem Semantics.fnsNoExs_of_sortedOKCl {c : Semantics} (h : c.sortedOKCl = true) : c.FnsNoExs :=
  fun f hf cl hcl => (Semantics.clausePlainOpen_partsP ((Semantics.sortedOKCl_parts h).2.1 f hf cl hcl).2).1

/-- What `sortedOKClEx` asks of an open generator (`paramsPlain`'s raw branch). -/
theorem Semantics.raw_of_sortedOKClEx {c : Semantics} (h : c.sortedOKClEx = true) {k : ParamSig}
    (hk : k ∈ c.params) (hr : k.raw = true) :
    k.impl = none ∧
    ((k.assoc || k.idem) = true → k.sig.args = [k.sig.result, k.sig.result]) ∧
    nRegSyms ≤ k.sig.name ∧ iteSort? (c.symName k.sig.name) = none ∧
    c.shapesOK = true :=
  Semantics.raw_of_paramsPlain (Semantics.sortedOKClEx_parts h).2.2.2.2 hk hr

namespace Faithful

variable {c : Semantics}

/-- `rule_ctx` from `sortedOKClEx`. -/
theorem rule_ctxClEx (hok : c.sortedOKClEx = true) {r : Rule} (hr : r ∈ c.rules) :
    sortOfTerm c.patCtxAll r.vars r.lhs = some topCellSort ∧
      (∀ t, r.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool) ∧
      sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.rhs = some topCellSort := by
  obtain ⟨-, -, hrs, -, -⟩ := Semantics.sortedOKClEx_parts hok
  have h := List.all_eq_true.mp hrs r hr
  simp only [Semantics.ruleSorted, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, -⟩, -⟩, -⟩, hreq⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hrhs⟩ := h
  refine ⟨hl, fun t ht => ?_, hrhs⟩
  · rw [ht] at hreq
    simpa [reqOK] using hreq

/-- `rule_ctx` from `sortedOKCl`. -/
theorem rule_ctxCl (hok : c.sortedOKCl = true) {r : Rule} (hr : r ∈ c.rules) :
    sortOfTerm c.patCtxAll r.vars r.lhs = some topCellSort ∧
      (∀ t, r.req = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool) ∧
      sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.rhs = some topCellSort :=
  rule_ctxClEx (Semantics.sortedOKClEx_of_sortedOKCl hok) hr

/-- `rule_ctx_ens` from `sortedOKClEx`. -/
theorem rule_ctx_ensClEx (hok : c.sortedOKClEx = true) {r : Rule} (hr : r ∈ c.rules) :
    ∀ t, r.ens = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool := by
  obtain ⟨-, -, hrs, -, -⟩ := Semantics.sortedOKClEx_parts hok
  have h := List.all_eq_true.mp hrs r hr
  simp only [Semantics.ruleSorted, Bool.and_eq_true, beq_iff_eq] at h
  intro t ht
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, hens⟩, -⟩, -⟩, -⟩, -⟩ := h
  rw [ht] at hens
  simpa [reqOK] using hens

/-- `rule_ctx_ens` from `sortedOKCl`. -/
theorem rule_ctx_ensCl (hok : c.sortedOKCl = true) {r : Rule} (hr : r ∈ c.rules) :
    ∀ t, r.ens = some t → sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars t = some Srt.bool :=
  rule_ctx_ensClEx (Semantics.sortedOKClEx_of_sortedOKCl hok) hr

end Faithful

/-- **What evaluation needs, from `sortedOKClEx` and `srReady`** (`sortCtx_of_all`): of each clause
it reads the right side's sort. -/
theorem sortCtx_of_allClEx {c : Semantics} (hok : c.sortedOKClEx = true) (hr : c.srReady = true)
    (hov : c.OvlCase) : SortCtx c := by
  simp only [Semantics.srReady, Bool.and_eq_true, List.all_eq_true] at hr
  obtain ⟨⟨hnd, htr⟩, hrk⟩ := hr
  obtain ⟨-, hfns, -, -, -⟩ := Semantics.sortedOKClEx_parts hok
  have htr' : ∀ a b d, (a, b) ∈ c.subsorts → (b, d) ∈ c.subsorts → (a, d) ∈ c.subsorts := fun a b d hab hbd => by
    have := htr (a, b) hab (b, d) hbd
    simp only [bne_self_eq_false, Bool.false_or, List.contains_iff_mem] at this
    exact this
  refine ⟨htr', nodup_of_eq_true hnd, fun fn hfn' => ?_, hov, rangeBelow_of_keysOK hrk⟩
  rcases List.mem_append.mp hfn' with hfn | hfn
  · refine ⟨c.fns.map Fn.sig, fun k hk => ?_, fun cl hcl => ?_⟩
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
      exact ⟨g, List.mem_append_left _ hg, rfl⟩
    · exact (Semantics.clauseSortedOpen_parts (hfns fn hfn cl hcl).1).2.2.2.1
  · exact ⟨[], fun k hk => (nomatch hk), fun cl h => (sortPreds_ctx hfn cl h).2.2.2.2.1⟩

/-- **What evaluation needs, from `sortedOKCl` and `srReady`** (`sortCtx_of_all`): of each clause
it reads the right side's sort. -/
theorem sortCtx_of_allCl {c : Semantics} (hok : c.sortedOKCl = true) (hr : c.srReady = true)
    (hov : c.OvlCase) : SortCtx c :=
  sortCtx_of_allClEx (Semantics.sortedOKClEx_of_sortedOKCl hok) hr hov

/-- `rhs_sorted_core` from `sortedOKClEx`. -/
theorem rhs_sorted_coreClEx {c : Semantics} (hok : c.sortedOKClEx = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    {r : Rule} (hr : r ∈ c.rules) {σ : Subst} (hσ : c.WellSorted r.vars σ) {v : GroundTerm}
    (he : EvalTerm c σ r.rhs (some v)) : c.sortOf v = some topCellSort :=
  EvalTerm.sorted (sortCtx_of_allClEx hok hsr hov) he
    (fun k hk => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk; exact ⟨g, List.mem_append_left _ hg, rfl⟩) hσ
    (Faithful.rule_ctxClEx hok hr).2.2 rfl

/-- `rhs_sorted_core` from `sortedOKCl`. -/
theorem rhs_sorted_coreCl {c : Semantics} (hok : c.sortedOKCl = true) (hsr : c.srReady = true) (hov : c.OvlCase)
    {r : Rule} (hr : r ∈ c.rules) {σ : Subst} (hσ : c.WellSorted r.vars σ) {v : GroundTerm}
    (he : EvalTerm c σ r.rhs (some v)) : c.sortOf v = some topCellSort :=
  rhs_sorted_coreClEx (Semantics.sortedOKClEx_of_sortedOKCl hok) hsr hov hr hσ he

end KCore
