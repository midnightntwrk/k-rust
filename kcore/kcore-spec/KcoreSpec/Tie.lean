/-
  KCore. The tie between a KORE text and its core (KCORE-SPEC.md §1). Reviewed layer. A KORE
  text k is tied (`Tied k`) when `parse k = .ok d`, `wf d`, and `Reordered d.emit k`: the core
  `d` prints back to k up to the order of its sentences, so what `Step` reads is what the KORE
  says.
-/
import KcoreSpec.Parse
import KcoreSpec.Kore.Reorder
import KcoreSpec.Kore.Translate
import KcoreSpec.Kore.Blocks
import KcoreSpec.Kore.Distinct
import KcoreSpec.FaithOK

set_option autoImplicit false

namespace KCore

/-- No user constructor or function is named like an interpreted hooked symbol (`hookSigs`).
Evaluation reads such a name as the hook (`isHook`, Evaluation.lean; the names it reads are exactly
`hookSigs`', `isHook_iff` in HooksApart.lean), whatever the definition declares; when the
definition's imports do not declare that hook, the name would be the user's symbol
in the KORE, with the user's clauses, and the hook in `Step`. Rejecting the name keeps the two
the same (KCORE-SPEC.md §7). -/
def Semantics.hooksApart (c : Semantics) : Bool :=
  c.ctors.all (fun k => !hookSigs.any (·.name == k.name)) &&
    c.fns.all (fun f => !hookSigs.any (·.name == f.label))

/-- The functions evaluation reads (`Semantics.allFns`: the user's, then the generated sort
predicates) have distinct labels. `lookupFn` takes the first function of a label, so a user
function named like a sort predicate (`LblisInt`), or a user sort named like a library sort (two
predicates `LblisInt`), would make "the function f" ambiguous between the core and the KORE. The
declaration check of `namesOK` excludes both whenever the fixed text declares the library's sorts
and their predicates, as the six texts do; `predsApart` states it on the core, where evaluation
reads it (KCORE-SPEC.md §7). -/
def Semantics.predsApart (c : Semantics) : Bool := nodup (c.allFns.map (·.label))

/-- Every sort and symbol the emitted KORE declares is declared once, no user symbol is named
like an interpreted hook (`hooksApart`), and the functions evaluation reads are named apart
(`predsApart`). -/
def Definition.namesOK (d : Definition) : Bool :=
  let D := d.emit
  KoreAML.nodup (D.sortDecls.map (·.name)) && KoreAML.nodup (D.symbolDecls.map (·.name) ++ D.aliasNames) &&
    d.sem.hooksApart && d.sem.predsApart && d.sem.idsOK

/-- Which variables the left side of a rule leaves open the values decide, an existential variable
of the right side among them: each is held by the right side under constructors, injections and
the symbols under which a value's element has values' elements as arguments (`heldOccs`), or of a
confined sort, or held by closed conditions (`OpenDecided`) no variable of which the right side, the
`ensures` or `post` holds; and a rule that competes with a larger one has open condition variables
of confined sorts, or closed conditions. A rule's predicates `pre` and `post` are not asked to be
`\top`. -/
def Semantics.rulesPlain (c : Semantics) : Bool := c.rules.all fun r =>
  let conf := fun i => (r.vars[i]?.map c.confined).getD false
  let rest := varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++ varOccsCond r.vars.length r.post
  let condApart := r.reqClosed && r.condVars.all fun j => !rest.contains j
  r.opens.all (fun i => (heldOccs c r.rhs).contains i || conf i || (r.condVars.contains i && condApart)) &&
  (!r.reqOpen || !c.rules.any (fun r' => r.prio < r'.prio) || r.openCondVars.all conf || r.reqClosed)

/-- Clauses bind no variable by `\exists` and have no predicate on the right side; a clause with a
predicate in its premise is not one whose conditions need a witness (`needsWitness`); and a clause's
open condition variables are of confined sorts, or its conditions are closed (`OpenDecided`). -/
def Semantics.clausesPlain (c : Semantics) : Bool := c.fns.all fun f => f.clauses.all fun cl =>
  cl.exs.isEmpty && (cl.pre.isTop || !cl.needsWitness c) && cl.post.isTop &&
  (!cl.reqOpen || cl.reqClosed ||
    cl.openCondVars.all fun i => (cl.vars[i]?.map c.confined).getD false)

/-- Every clause's predicate is `\top`: what the checks outside `coreOK` ask of the clauses (`ok`,
`okM`, `okAll`), and the statements whose proofs read no predicate of a clause. -/
def Semantics.clausesPreTop (c : Semantics) : Bool :=
  c.fns.all fun f => f.clauses.all fun cl => cl.pre.isTop

theorem Semantics.clausesPreTop_spec {c : Semantics} (h : c.clausesPreTop = true) {f : Fn} (hf : f ∈ c.fns)
    {cl : Clause} (hcl : cl ∈ f.clauses) : cl.pre = .top :=
  Cond.eq_top_of_isTop (List.all_eq_true.mp (List.all_eq_true.mp h f hf) cl hcl)

/-- Each sort hooked to a library carrier is an own sort of the definition, named once, neither a
token, a byte nor a collection sort, and its carrier is Int, Bool, Float, String or Bytes. -/
def Semantics.carriersOK (c : Semantics) : Bool :=
  c.lib.carriers.all (fun p => decide (nRegSorts ≤ p.1) && c.userSorts.contains p.1 &&
    [Srt.int, Srt.bool, Srt.float, Srt.string, Srt.bytes].contains p.2 &&
    !c.lib.tokenSorts.contains p.1 && !c.lib.byteSorts.contains p.1 && !c.colls.any (·.sort == p.1)) &&
  nodup (c.lib.carriers.map (·.1))

/-- The parameters' shapes, and the carriers. A parameter that is no open generator has no
associativity or idempotence axiom. An open generator (`raw`) has no registry hook,
two arguments of its result sort where it has a law (associativity, idempotence or both), a number outside the registry (so `lookupOpen`
answers for it) and no name like an `ite`'s (`iteSort?`), and the semantics has `shapesOK` (no value
of a sort the library's sentences read, other than Float, applies it). The sorts hooked to a
library carrier are well formed (`carriersOK`). -/
def Semantics.paramsPlain (c : Semantics) : Bool :=
  c.params.all (fun k =>
    if k.raw then k.impl.isNone &&
      (!(k.assoc || k.idem) || k.sig.args == [k.sig.result, k.sig.result]) &&
      decide (nRegSyms ≤ k.sig.name) && (iteSort? (c.symName k.sig.name)).isNone &&
      c.shapesOK
    else !k.assoc && !k.idem) && c.carriersOK

/-- The core is well-formed: declarations over declared sorts, its rules, clauses and parameters
plain (`rulesPlain`, `clausesPlain`, `paramsPlain`), every clause's predicate `\top`
(`clausesPreTop`), subsorts, functions and rules. No sort is
required to have a value (`Semantics.valueless`, which the account prints). -/
def Semantics.ok (c : Semantics) : Bool :=
  c.declsOK && (c.rulesPlain && (c.clausesPlain && c.clausesPreTop) && c.paramsPlain) && c.subsortsOK && c.fnsOK &&
    c.rules.all c.ruleOK

namespace Semantics
variable (c : Semantics)

/-- Every term of a condition is well sorted: a term at the sort its connective names, over the
right-hand side's context, and a pattern of an `exMatch` over a left-hand side's (`patCtxAll`);
a binder extends the variable sorts by the sorts it binds. The sort an atom names is a numbered
sort of the definition (`s < nRegSorts + c.sortNames.length`): a condition about a sort the
definition does not have states nothing about its values, and through it every variable the
condition holds has a numbered sort. -/
def condOK (vars : List Srt) : Cond → Bool
  | .top | .bot => true
  | .not p => condOK vars p
  | .and p q | .or p q | .implies p q => condOK vars p && condOK vars q
  | .ceil s t => sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t == some s &&
      decide (s < nRegSorts + c.sortNames.length)
  | .equals s t u | .mem s t u =>
      (sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t == some s &&
      sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars u == some s) &&
      decide (s < nRegSorts + c.sortNames.length)
  | .exMatch ys s p t body =>
      (sortOfTerm c.patCtxAll (vars ++ ys) p == some s &&
      sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) vars t == some s && condOK (vars ++ ys) body) &&
      decide (s < nRegSorts + c.sortNames.length)
  | .ex s body | .all s body => condOK (vars ++ [s]) body

/-- A clause of `f` is well sorted over the function signatures `rhsHeads`: its patterns have the
argument sorts in a left-hand side's context (`patCtxAll`), each of its variables occurs in it (in
its patterns, its conditions, its right-hand side, its `ensures` or its right side's predicate), its
`requires` is a Bool, its right-hand side has the result sort, its `ensures` is a Bool, each
binder of its premise's and its right side's predicates ranges where values and elements agree
(`Cond.bound`), and its premise's predicate is well sorted (`condOK`). -/
def clauseSorted (f : Fn) (rhsHeads : List CtorSig) (cl : Clause) : Bool :=
  sortsOfTerms c.patCtxAll cl.vars cl.pats == some f.args &&
  binds cl.vars.length (varOccsList cl.pats ++ cl.condVars ++ varOccs cl.rhs ++
    (cl.ens.map varOccs).getD [] ++ varOccsCond cl.vars.length cl.post) &&
  reqOK (c.rhsCtx rhsHeads) cl.vars cl.req &&
  sortOfTerm (c.rhsCtx rhsHeads) cl.vars cl.rhs == some f.result &&
  reqOK (c.rhsCtx rhsHeads) cl.vars cl.ens &&
  (Cond.bound c cl.vars.length cl.pre && Cond.bound c cl.vars.length cl.post) &&
  condOK c cl.vars cl.pre

/-- A rule's predicates are well sorted (`condOK`), with binders that range where values and
elements agree (`Cond.bound`): what `ruleSorted` asks of `pre` and `post`. -/
def rulePredsOK (r : Rule) : Bool :=
  c.condOK r.vars r.pre && c.condOK r.vars r.post &&
  Cond.bound c r.vars.length r.pre && Cond.bound c r.vars.length r.post

/-- `\top` predicates are well sorted. -/
theorem rulePredsOK_top {r : Rule} (hpre : r.pre = .top) (hpost : r.post = .top) :
    c.rulePredsOK r = true := by
  simp [rulePredsOK, hpre, hpost, condOK, Cond.bound]

/-- A rule is well sorted: its left-hand side has the configuration sort in a left-hand side's
context (`patCtxAll`), each of its variables occurs in it, its existential variables are distinct
variables the left side and the conditions do not hold, its `requires` and its `ensures` are
Bools and its predicates well sorted (`condOK`) with binders that range where values and elements
agree (`Cond.bound`), and its right-hand side has the configuration sort, over the constructors,
hooks, parameters and functions. -/
def ruleSorted (r : Rule) : Bool :=
  sortOfTerm c.patCtxAll r.vars r.lhs == some topCellSort &&
  binds r.vars.length (varOccs r.lhs ++ r.condVars ++ varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++
    varOccsCond r.vars.length r.post) &&
  nodup r.exs && r.exs.all (fun i => r.opens.contains i && !r.condVars.contains i) &&
  reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.req && condOK c r.vars r.pre &&
  reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.ens && condOK c r.vars r.post &&
  Cond.bound c r.vars.length r.pre && Cond.bound c r.vars.length r.post &&
  sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.rhs == some topCellSort

/-- **The semantics is well sorted**: its subsorts are a strict partial order into its own sorts
and the library's sorts of constructor terms (`subsortsOK`), and every clause of every function and every rule is well sorted, binding each of
its variables (`clauseSorted`, `ruleSorted`); and its rules, clauses and parameters are plain
(`rulesPlain`, `clausesPlain`, `paramsPlain`). -/
def sortedOK : Bool :=
  c.subsortsOK && c.fns.all (fun f => f.clauses.all (c.clauseSorted f (c.fns.map Fn.sig))) &&
    c.rules.all c.ruleSorted && c.rulesPlain && c.clausesPlain && c.paramsPlain

/-- What `sortedOK` says of the sorts, the clauses and the rules. -/
theorem sortedOK_sorted {c : Semantics} (h : c.sortedOK = true) :
    (c.subsortsOK && c.fns.all (fun f => f.clauses.all (c.clauseSorted f (c.fns.map Fn.sig))) &&
      c.rules.all c.ruleSorted) = true := by
  simp only [sortedOK, Bool.and_eq_true] at h ⊢; exact h.1.1.1

/-- Each clause's predicate, in a semantics `sortedOK` accepts, is well sorted over the clause's
variables (`condOK`), with binders that range where values and elements agree (`Cond.bound`). -/
theorem sortedOK_clausePre {c : Semantics} (h : c.sortedOK = true) {fn : Fn} (hfn : fn ∈ c.fns)
    {cl : Clause} (hcl : cl ∈ fn.clauses) :
    c.condOK cl.vars cl.pre = true ∧ Cond.bound c cl.vars.length cl.pre = true := by
  have hs := sortedOK_sorted h
  simp only [Bool.and_eq_true, List.all_eq_true] at hs
  have := hs.1.2 fn hfn cl hcl
  simp only [clauseSorted, Bool.and_eq_true] at this
  exact ⟨this.2, this.1.2.1⟩

/-- Rules whose predicates `Cond.isTop` accepts have `\top` predicates: the decidable form of the
hypothesis the lemmas for rules without predicates take. -/
theorem rulesTop_of_isTop {c : Semantics}
    (h : c.rules.all (fun r => r.pre.isTop && r.post.isTop) = true) :
    ∀ r ∈ c.rules, r.pre = .top ∧ r.post = .top := fun r hr => by
  have hr' := List.all_eq_true.mp h r hr
  simp only [Bool.and_eq_true] at hr'
  exact ⟨Cond.eq_top_of_isTop hr'.1, Cond.eq_top_of_isTop hr'.2⟩

/-- Each variable of a rule of a semantics `sortedOK` accepts occurs in its left side, its
`requires`, its right side, its `ensures` or its `post`. -/
theorem sortedOK_rule_occurs {c : Semantics} (h : c.sortedOK = true) {r : Rule} (hr : r ∈ c.rules) :
    binds r.vars.length (varOccs r.lhs ++ r.condVars ++ varOccs r.rhs ++ (r.ens.map varOccs).getD [] ++
      varOccsCond r.vars.length r.post) = true := by
  have hs := sortedOK_sorted h
  simp only [Bool.and_eq_true, List.all_eq_true] at hs
  have hrs := hs.2 r hr
  simp only [ruleSorted, Bool.and_eq_true] at hrs
  exact hrs.1.1.1.1.1.1.1.1.1.2

/-- A rule with `ruleSorted` and no open variable has no existential variable. -/
theorem exs_nil_of_opens {c : Semantics} {r : Rule} (hs : c.ruleSorted r = true) (hop : r.opens = []) :
    r.exs = [] := by
  simp only [ruleSorted, Bool.and_eq_true, List.all_eq_true] at hs
  have hx := hs.1.1.1.1.1.1.1.2
  match hr : r.exs with
  | [] => rfl
  | i :: _ =>
    have hi := (hx i (by rw [hr]; exact List.mem_cons_self ..)).1
    simp [hop] at hi

/-- A rule with `ruleSorted` whose left side binds every variable has no existential variable: an
existential variable is one the left side leaves open (`ruleSorted`), and it leaves none. -/
theorem exs_nil_of_binds {c : Semantics} {r : Rule} (hs : c.ruleSorted r = true)
    (hb : binds r.vars.length (varOccs r.lhs) = true) : r.exs = [] :=
  exs_nil_of_opens hs (by
    simp only [Rule.opens, List.filter_eq_nil_iff, List.mem_range, Bool.not_eq_eq_eq_not, Bool.not_true,
      Bool.not_eq_false]
    intro i hi
    simpa using List.all_eq_true.mp hb i (List.mem_range.mpr hi))

/-- A rule of a semantics `sortedOK` accepts whose left side binds every variable has no existential
variable (`exs_nil_of_binds`). -/
theorem sortedOK_exsNil {c : Semantics} (h : c.sortedOK = true) {r : Rule} (hr : r ∈ c.rules)
    (hb : binds r.vars.length (varOccs r.lhs) = true) : r.exs = [] := by
  have hs := sortedOK_sorted h
  simp only [Bool.and_eq_true, List.all_eq_true] at hs
  exact exs_nil_of_binds (hs.2 r hr) hb

theorem clauseSorted_of_all {f : Fn} {H : List CtorSig} {cl : Clause} (h : c.clauseOKAll f H cl = true)
    (hb : (Cond.bound c cl.vars.length cl.pre && Cond.bound c cl.vars.length cl.post) = true)
    (hc : c.condOK cl.vars cl.pre = true) :
    c.clauseSorted f H cl = true := by
  simp only [clauseOKAll, clauseSorted, Bool.and_eq_true] at h hb ⊢
  refine ⟨⟨⟨⟨⟨⟨h.1.1.1.1.1, ?_⟩, h.1.1.2⟩, h.1.2⟩, h.2⟩, hb⟩, hc⟩
  have hbd := h.1.1.1.2
  simp only [binds, List.all_eq_true, List.contains_iff_mem, List.mem_append, Clause.leftVars] at hbd ⊢
  intro i hi
  rcases hbd i hi with ((h1 | h1) | h1) | h1
  · exact Or.inl (Or.inl (Or.inl (Or.inl h1)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr h1)))
  · exact Or.inl (Or.inl (Or.inr h1))
  · exact Or.inl (Or.inr h1)

/-- A clause whose predicates are `\top` has its binders where values and elements agree
(`Cond.bound`): it has none; `clausesPlain` gives the right side's, `clausesPreTop` the premise's. -/
theorem clauseBound_of_plain (hp : c.clausesPlain = true) (ht : c.clausesPreTop = true) {f : Fn} (hf : f ∈ c.fns)
    {cl : Clause} (hcl : cl ∈ f.clauses) :
    (Cond.bound c cl.vars.length cl.pre && Cond.bound c cl.vars.length cl.post) = true := by
  simp only [clausesPlain, Bool.and_eq_true, List.all_eq_true] at hp
  obtain ⟨⟨-, hpost⟩, -⟩ := hp f hf cl hcl
  rw [clausesPreTop_spec ht hf hcl, Cond.eq_top_of_isTop hpost]
  rfl

/-- A clause whose premise's predicate is `\top` (`clausesPreTop`) has it well sorted (`condOK`). -/
theorem clausePreOK_of_plain (ht : c.clausesPreTop = true) {f : Fn} (hf : f ∈ c.fns) {cl : Clause}
    (hcl : cl ∈ f.clauses) : c.condOK cl.vars cl.pre = true := by
  rw [clausesPreTop_spec ht hf hcl]
  rfl

/-- `ruleOKAll` and `rulePredsOK` give `ruleSorted`: `ruleOKAll` checks the existential variables
as `ruleSorted` does, and `rulePredsOK` the predicates. -/
theorem ruleSorted_of_allPreds {r : Rule} (h : c.ruleOKAll r = true) (hp : c.rulePredsOK r = true) :
    c.ruleSorted r = true := by
  simp only [ruleOKAll, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, -⟩, h3⟩, h4⟩, h5⟩, h6⟩, hn⟩, hx⟩ := h
  simp only [rulePredsOK, Bool.and_eq_true] at hp
  obtain ⟨⟨⟨p1, p2⟩, p3⟩, p4⟩ := hp
  simp only [ruleSorted, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h3⟩, hn⟩, hx⟩, h4⟩, p1⟩, h5⟩, p2⟩, p3⟩, p4⟩, h6⟩

/-- `ruleOKAll` with `\top` predicates gives `ruleSorted` (`ruleSorted_of_allPreds`). -/
theorem ruleSorted_of_allTop {r : Rule} (h : c.ruleOKAll r = true) (hpre : r.pre = .top)
    (hpost : r.post = .top) : c.ruleSorted r = true :=
  c.ruleSorted_of_allPreds h (c.rulePredsOK_top hpre hpost)

theorem ruleSorted_of_all {r : Rule} (h : c.ruleOKAll r = true) (_hex : r.exs = []) (hpre : r.pre = .top)
    (hpost : r.post = .top) : c.ruleSorted r = true :=
  c.ruleSorted_of_allTop h hpre hpost

/-- What `ruleSorted` says of a rule's left side, its `requires`, its `ensures` and its right side. -/
theorem ruleSorted_parts {r : Rule} (h : c.ruleSorted r = true) :
    sortOfTerm c.patCtxAll r.vars r.lhs = some topCellSort ∧
      reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.req = true ∧
      reqOK (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.ens = true ∧
      sortOfTerm (c.rhsCtx (c.fns.map Fn.sig)) r.vars r.rhs = some topCellSort := by
  simp only [ruleSorted, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, -⟩, -⟩, -⟩, hreq⟩, -⟩, hens⟩, -⟩, -⟩, -⟩, hrhs⟩ := h
  exact ⟨hl, hreq, hens, hrhs⟩

end Semantics

/-- The definition is well-formed: as `ok`, with the rules' left-hand sides well-sorted over the
collection pattern symbols too (`ruleOKAll`: a list's `ListItem(P) L`, a cell map's) and the rules'
predicates well sorted (`rulePredsOK`). `ok` is the narrower condition the executable matcher's
theorems read; `okAll` is what the tie checks. -/
def Semantics.okAll (c : Semantics) : Bool :=
  c.declsOK && (c.rulesPlain && (c.clausesPlain && c.clausesPreTop) && c.paramsPlain) && c.subsortsOK && c.fnsOKAll &&
    c.rules.all c.ruleOKAll && c.rules.all c.rulePredsOK

/-- The rules, clauses and parameters of a core `okAll` accepts are plain. -/
theorem Semantics.plain_of_okAll {c : Semantics} (h : c.okAll = true) :
    c.rulesPlain = true ∧ c.clausesPlain = true ∧ c.paramsPlain = true := by
  simp only [Semantics.okAll, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.2.1.1, h.1.1.1.1.2.1.2.1, h.1.1.1.1.2.2⟩

/-- Every clause of a core `okAll` accepts has the predicate `\top`. -/
theorem Semantics.preTop_of_okAll {c : Semantics} (h : c.okAll = true) : c.clausesPreTop = true := by
  simp only [Semantics.okAll, Bool.and_eq_true] at h
  exact h.1.1.1.1.2.1.2.2

theorem Semantics.okAll_of_ok {c : Semantics} (h : c.ok = true) : c.okAll = true := by
  simp only [Semantics.ok, Semantics.okAll, Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨⟨⟨h.1.1, c.fnsOKAll_of h.1.2⟩, fun r hr => c.ruleOKAll_of (h.2 r hr)⟩, fun r hr => ?_⟩
  have hro := h.2 r hr
  simp only [Semantics.ruleOK, Bool.and_eq_true] at hro
  exact c.rulePredsOK_top (Cond.eq_top_of_isTop hro.1.2) (Cond.eq_top_of_isTop hro.2)

/-- **The readiness condition of the ok track without the `\top` shape**: as `ok`, with each rule
`ruleOKM` (`ruleOK` less its two `\top` predicates) and its predicates well sorted
(`rulePredsOK`). -/
def Semantics.okM (c : Semantics) : Bool :=
  c.declsOK && (c.rulesPlain && (c.clausesPlain && c.clausesPreTop) && c.paramsPlain) && c.subsortsOK && c.fnsOK &&
    c.rules.all c.ruleOKM && c.rules.all c.rulePredsOK

theorem Semantics.okM_of_ok {c : Semantics} (h : c.ok = true) : c.okM = true := by
  simp only [Semantics.ok, Semantics.okM, Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨⟨h.1, fun r hr => (c.ruleOK_iff.mp (h.2 r hr)).1⟩, fun r hr => ?_⟩
  obtain ⟨-, hpre, hpost⟩ := c.ruleOK_iff.mp (h.2 r hr)
  exact c.rulePredsOK_top (Cond.eq_top_of_isTop hpre) (Cond.eq_top_of_isTop hpost)

theorem Semantics.okAll_of_okM {c : Semantics} (h : c.okM = true) : c.okAll = true := by
  simp only [Semantics.okM, Semantics.okAll, Bool.and_eq_true, List.all_eq_true] at h ⊢
  exact ⟨⟨⟨h.1.1.1, c.fnsOKAll_of h.1.1.2⟩, fun r hr => c.ruleOKAll_of_M (h.1.2 r hr)⟩, h.2⟩

/-- A rule of a semantics `okM` accepts has no existential variable and a left side that binds
every variable (`ruleOKM`). -/
theorem Semantics.okM_rule {c : Semantics} (h : c.okM = true) {r : Rule} (hr : r ∈ c.rules) :
    r.exs = [] ∧ binds r.vars.length (varOccs r.lhs) = true := by
  simp only [Semantics.okM, Bool.and_eq_true, List.all_eq_true] at h
  have hro := h.1.2 r hr
  simp only [Semantics.ruleOKM, Bool.and_eq_true] at hro
  exact ⟨List.isEmpty_iff.mp hro.2, hro.1.1.1.1.2⟩

/-- `okAll` checks each condition of `sortedOK`. -/
theorem Semantics.sortedOK_of_okAll {c : Semantics} (h : c.okAll = true) : c.sortedOK = true := by
  obtain ⟨hrp, hcp, hpp⟩ := Semantics.plain_of_okAll h
  have hpt := Semantics.preTop_of_okAll h
  simp only [Semantics.okAll, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨-, hs⟩, hf⟩, hr⟩, hq⟩ := h
  simp only [Semantics.fnsOKAll, List.all_eq_true] at hf
  simp only [Semantics.sortedOK, Bool.and_eq_true, List.all_eq_true, hrp, hcp, hpp, and_true]
  refine ⟨⟨hs, fun f hf' cl hcl => ?_⟩, fun r hr' =>
    c.ruleSorted_of_allPreds (List.all_eq_true.mp hr r hr') (List.all_eq_true.mp hq r hr')⟩
  have := hf f hf'
  simp only [Semantics.fnOKAll, Bool.and_eq_true, List.all_eq_true] at this
  exact c.clauseSorted_of_all (this.1 cl hcl) (c.clauseBound_of_plain hcp hpt hf' hcl) (c.clausePreOK_of_plain hpt hf' hcl)

/-- A rule of a semantics `ok` accepts has the plain shapes and a left side that binds every
variable (`ruleOK`). -/
theorem Semantics.ok_rule {c : Semantics} (h : c.ok = true) {r : Rule} (hr : r ∈ c.rules) :
    r.exs = [] ∧ r.pre = .top ∧ r.post = .top ∧ binds r.vars.length (varOccs r.lhs) = true := by
  simp only [Semantics.ok, Bool.and_eq_true, List.all_eq_true] at h
  have hro := h.2 r hr
  simp only [Semantics.ruleOK, Bool.and_eq_true] at hro
  exact ⟨List.isEmpty_iff.mp hro.1.1.2, Cond.eq_top_of_isTop hro.1.2, Cond.eq_top_of_isTop hro.2,
    hro.1.1.1.1.1.1.2⟩

/-- The functions declared `hooked-symbol` (their presentation carries a `hook{}` attribute) name
hooks no registry hook interprets (`regHookOf`). Such a function's meaning is its clauses and,
where none applies, the interpretation's value; a hook the registry interprets would give the
symbol the registry's graph as well, which the core does not state of a function. -/
def Definition.hookFnsUnregOK (d : Definition) : Bool :=
  d.pres.fns.all fun fp => fp.hook.all fun h => (regHookOf h).isNone

/-- A parameter symbol's argument or result sort: a declared sort below KItem, K or KItem. Unlike a
constructor's, it may be a sort of which KCore represents no value (List): the symbol is then
never applied, or never defined (`paramVal` keeps only values of its sort). -/
def Semantics.paramSortOK (c : Semantics) (s : Srt) : Bool :=
  [Srt.k, Srt.kitem].contains s || c.userSorts.contains s || c.lib.sortsBelowKItem.contains s

/-- The arguments of a collection sort's element symbol: a map's key and value sorts, a set's or a
list's element sort; `none` when its value sort is not as its kind has it (a map has one, a set or
a list none). -/
def CollSig.elemArgs (k : CollSig) : Option (List Srt) :=
  match k.kind, k.val with
  | .map, some v => some [k.key, v]
  | .set, none | .list, none => some [k.key]
  | _, _ => none

/-- A collection sort of the definition: one of its sorts, with a value sort exactly when it is a
map (`CollSig.elemArgs`), whose unit, element and concatenation are parameter symbols of its sort
implemented by the hooks of its kind (`MAP.unit`, `MAP.element`, `MAP.concat` for a map), so its
values are built and read as the library's collections are. -/
def Semantics.collOK (c : Semantics) (k : CollSig) : Bool :=
  let b := builtinColl k.kind
  match k.elemArgs with
  | none => false
  | some elemArgs =>
    c.userSorts.contains k.sort &&
    c.params.contains { sig := ⟨k.unit, [], k.sort⟩, impl := some b.unit } &&
    c.params.contains { sig := ⟨k.elem, elemArgs, k.sort⟩, impl := some b.elem } &&
    c.params.contains { sig := ⟨k.concat, [k.sort, k.sort], k.sort⟩, impl := some b.concat }

/-- The parameter symbols: first those of the imported modules (registry numbers, each one of
`libParams`, Builtins.lean), then the user's (own numbers), whose sorts are declared ones, each with a presentation, and whose meaning
is the one its `hook{}` attribute names: the registry's hook when the registry interprets that
attribute and the symbol's sorts carry the sort hooks of that hook's sorts (`Parse.hookImplAt`), a
parameter otherwise; the collection sorts (`collOK`); and the functions
declared `hooked-symbol`, whose hooks the registry does not interpret (`hookFnsUnregOK`). -/
def Definition.paramsOK (d : Definition) : Bool :=
  let lib := d.sem.params.takeWhile fun k => decide (k.sig.name < nRegSyms)
  let own := d.sem.params.drop lib.length
  let stands := d.sem.colls.map (fun k => (k.sort, (builtinColl k.kind).sort)) ++ d.sem.lib.carriers
  lib.all (libParams d.pres.imports).contains &&
  own.all (fun k => decide (nRegSyms ≤ k.sig.name)) &&
  own.length == d.pres.params.length &&
  (withPres own d.pres.params).all (fun (k, pp) =>
    k.sig.args.all d.sem.paramSortOK && d.sem.paramSortOK k.sig.result && k.impl == Parse.hookImplAt stands pp.hook k.sig) &&
  -- the collection sorts: distinct, and each built by its symbols
  nodup (d.sem.colls.map (·.sort)) && d.sem.colls.all d.sem.collOK &&
  d.hookFnsUnregOK

/-- `wf`'s conditions, each by name: one row for each conjunct of `wf` and of `okAll`, and the
conjuncts of `faithOK`, so that a definition `wf` refuses has a failing row. -/
def Definition.report (d : Definition) : List (String × Bool) :=
  [("names declared once, none named like a hook, functions named apart, own sorts and symbols numbered in order", d.namesOK),
   ("declarations over declared sorts", d.sem.declsOK),
   ("rules plain (rulesPlain): open and existential variables held, open condition variables confined or closed conditions apart", d.sem.rulesPlain),
   ("clauses plain (clausesPlain): no existential variable, \\top predicates, open condition variables confined or closed conditions", d.sem.clausesPlain),
   ("parameters plain (paramsPlain): no law on a parameter that is no open generator, an open generator of the admitted shape; carriers well formed", d.sem.paramsPlain),
   ("subsorts: a strict partial order into user sorts and library constructor sorts, closed", d.sem.subsortsOK),
   ("functions: well-sorted, covering", d.sem.fnsOKAll),
   ("rules: well-sorted over the configuration sort", d.sem.rules.all fun r => d.sem.ruleOKAll r && d.sem.rulePredsOK r),
   ("certificate: self calls decrease", d.cert.ok d.sem),
   ("presentation: variable names distinct; cells named apart, the cell holding $PGM of content K or its sort, each with its kind's sorts and symbols, the core's first sorts, constructors and subsorts", d.pres.ok d.sem),
   ("theory: no function or constructor named like ite at a sort, functions' sorts numbered", Faithful.namesNumbered d.sem),
   ("theory: values generated (constructor sorts)", Faithful.genWf d.sem),
   ("theory: no collection sort holds a domain value", Faithful.collSortsOK d.sem),
   ("theory: collections built by the parameters their names denote", Faithful.collsOK d.sem),
   ("theory: every left-hand-side head a constructor or read downwards", Faithful.patHeadsOK d.sem),
   ("theory: symbols and sorts named apart", Faithful.Model.namesApartK d.sem),
   ("theory: no token or byte sort is Int or Bool", Faithful.Model.LitsApart d.sem),
   ("theory: sorts of values and symbols numbered", Faithful.Model.sortsNumbered d.sem),
   ("theory: collection symbols apart from constructors", Faithful.Model.collsNotCtors d.sem),
   ("theory: symbols named like ite apart by their sort", Faithful.Model.itesApart d.sem),
   ("theory: hooks, parameters and constructors apart", Faithful.Model.kindsApart d.sem),
   ("theory: each constructor listed once", Faithful.Model.ctorsOnce d.sem),
   ("theory: functions apart from constructors, hooks and parameters", Faithful.Model.fnsApart d.sem),
   ("hooked functions: no registry hook interprets their hook", d.hookFnsUnregOK),
   ("parameter symbols (paramsOK): the imported modules' and the user's, each as its hook names", d.paramsOK),
   ("overloading symbols (overloadsOK)", d.sem.overloadsOK)]

/-- **A well-formed definition**: its names (`namesOK`), its core (`okAll`), its certificate, its
presentation and its parameters are well formed, its semantics meets the decidable conditions
of its matching-logic theory (`faithOK`), and its overloading symbols are well formed
(`overloadsOK`). -/
def wf (d : Definition) : Bool :=
  d.namesOK && d.sem.okAll && d.cert.ok d.sem && d.pres.ok d.sem && d.paramsOK && d.sem.faithOK &&
    d.sem.overloadsOK

theorem faithOK_of_wf {d : Definition} (h : wf d = true) : d.sem.faithOK = true := by
  unfold wf at h
  simp only [Bool.and_eq_true] at h
  exact h.1.2

/-- `Tied k`: k is the emitted KORE of a well-formed definition, up to sentence order.
Irreducible: unfolding it runs `parse` on k, which the elaborator would otherwise do whenever it
compares a type with `Tied k`; the kernel unfolds it all the same. -/
@[irreducible] def Tied (k : Kore.Definition) : Prop :=
  match Parse.parse k with
  | .ok d => wf d = true ∧ KoreAML.Reordered d.emit k
  | .error _ => False

instance (k : Kore.Definition) : Decidable (Tied k) := by
  unfold Tied
  cases Parse.parse k with
  | error => exact inferInstanceAs (Decidable False)
  | ok d => exact inferInstanceAs (Decidable (_ ∧ _))

theorem Tied.sound {k : Kore.Definition} (h : Tied k) : ∃ d, wf d = true ∧ KoreAML.Reordered d.emit k := by
  unfold Tied at h
  split at h
  · exact ⟨_, h⟩
  · exact h.elim

/-! ## The tie from its parts

A tie is checked in parts, each a decision of bounded size: `parse` (Parse.lean's stages), `wf`
conjunct by conjunct with the names' distinctness by codes (`KoreAML.Distinct`), and `Reordered`
from the user module's blocks compared with the KORE a slice at a time (`KoreAML.Blocks`). -/

theorem Tied.of_parts {k : Kore.Definition} {d : Definition} (hp : Parse.parse k = .ok d)
    (hw : wf d = true) (hr : KoreAML.Reordered d.emit k) : Tied k := by
  unfold Tied; rw [hp]; exact ⟨hw, hr⟩

theorem wf_of_parts {d : Definition} {p₁ p₂ : Nat}
    (hs : KoreAML.Distinct.codesDistinct p₁ (d.emit.sortDecls.map (·.name)) = true)
    (hy : KoreAML.Distinct.codesDistinct p₂ (d.emit.symbolDecls.map (·.name) ++ d.emit.aliasNames) = true)
    (hn : (d.sem.hooksApart && d.sem.predsApart && d.sem.idsOK) = true)
    (hok : d.sem.ok = true) (hc : d.cert.ok d.sem = true) (hpr : d.pres.ok d.sem = true)
    (hpa : d.paramsOK = true) (hfa : d.sem.faithOK = true) (hov : d.sem.overloadsOK = true) :
    wf d = true := by
  simp only [Bool.and_eq_true] at hn
  simp only [wf, Definition.namesOK, KoreAML.Distinct.nodup_of_codes hs, KoreAML.Distinct.nodup_of_codes hy,
    hn.1.1, hn.1.2, hn.2, Semantics.okAll_of_ok hok, hc, hpr, hpa, hfa, hov, Bool.and_self]

/-- `wf_of_parts` for a core outside `ok`, from `okAll`. -/
theorem wf_of_parts_all {d : Definition} {p₁ p₂ : Nat}
    (hs : KoreAML.Distinct.codesDistinct p₁ (d.emit.sortDecls.map (·.name)) = true)
    (hy : KoreAML.Distinct.codesDistinct p₂ (d.emit.symbolDecls.map (·.name) ++ d.emit.aliasNames) = true)
    (hn : (d.sem.hooksApart && d.sem.predsApart && d.sem.idsOK) = true)
    (hok : d.sem.okAll = true) (hc : d.cert.ok d.sem = true) (hpr : d.pres.ok d.sem = true)
    (hpa : d.paramsOK = true) (hfa : d.sem.faithOK = true) (hov : d.sem.overloadsOK = true) :
    wf d = true := by
  simp only [Bool.and_eq_true] at hn
  simp only [wf, Definition.namesOK, KoreAML.Distinct.nodup_of_codes hs, KoreAML.Distinct.nodup_of_codes hy,
    hn.1.1, hn.1.2, hn.2, hok, hc, hpr, hpa, hfa, hov, Bool.and_self]

/-- `Reordered d.emit k` from the user module's blocks: the prelude modules and the attributes
are the same, and the blocks are the KORE's segments in another order. -/
theorem reordered_of_blocks {d : Definition} {k : Kore.Definition} {mU : Kore.Module}
    {segs : List (List Kore.Sentence)} {n : Nat} {σ : List Nat}
    (hattr : d.emit.attributes = k.attributes)
    (hmods : k.modules = preludeModules ++ [mU])
    (hname : (userModule d.sem d.pres).name = mU.name)
    (hattrs : (userModule d.sem d.pres).attributes = mU.attributes)
    (hsents : mU.sentences = segs.flatten)
    (hlen : (userBlocks d.sem d.pres).length = n)
    (hslice : KoreAML.Blocks.SliceIs (userBlocks d.sem d.pres) segs 0 n σ)
    (hperm : σ.isPerm (List.range segs.length) = true) : KoreAML.Reordered d.emit k := by
  subst hlen
  have hp : (userModule d.sem d.pres).sentences.Perm mU.sentences := by
    have hu : (userModule d.sem d.pres).sentences = (userBlocks d.sem d.pres).flatten := by
      simp only [userModule]
    rw [hsents, hu]; exact KoreAML.Blocks.SliceIs.perm hslice hperm
  refine ⟨hattr, ?_, ?_⟩
  · simp only [Definition.emit, emit, hmods, List.length_append, List.length_singleton]
  · intro mm hm
    simp only [Definition.emit, emit, hmods, List.zip_append rfl, List.mem_append, List.zip_cons_cons,
      List.zip_nil_left, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
      simp only [List.getElem_zip] at he
      subst he
      exact ⟨rfl, rfl, List.Perm.refl _⟩
    · exact ⟨hname, hattrs, hp⟩

end KCore
